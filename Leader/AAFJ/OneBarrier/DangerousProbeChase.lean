import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OriginalDangerousProbeChase

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup (UniqueLeaderAt)

/-- New local endpoint predicate, not a pre-existing repository API. -/
def MultipleLeaders {n k : Nat} (C : Fin n → State k) : Prop :=
  ∃ a b : Fin n,
    a ≠ b ∧ (C a).leader = true ∧ (C b).leader = true

instance {n k : Nat} (C : Fin n → State k) :
    Decidable (MultipleLeaders C) := by
  unfold MultipleLeaders
  infer_instance

/-- A literal clockwise word, with no artificial transitions. -/
def walkWord {n : Nat} (ring : DirectedRing n) :
    Fin n → Nat → List (Fin n)
  | _, 0 => []
  | e, m + 1 => e :: walkWord ring (ring.rightNeighbor e) m

@[simp] theorem walkWord_length {n : Nat}
    (ring : DirectedRing n) (e : Fin n) (m : Nat) :
    (walkWord ring e m).length = m := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih =>
      simp only [walkWord, List.length_cons, ih]

def prefixWord {n : Nat} (ring : DirectedRing n)
    (b p : Fin n) : List (Fin n) :=
  walkWord ring (cutPos ring b p) (n - 1 - p.val)

def macroWord {n : Nat} (ring : DirectedRing n)
    (b p : Fin n) : List (Fin n) :=
  prefixWord ring b p ++ [b]

def macroBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (b p : Fin n) : Fin n :=
  let E := rawRun hk ring C (prefixWord ring b p)
  if AdvanceReady hk ring E b then ring.rightNeighbor b else b

theorem macroWord_length {n : Nat} (ring : DirectedRing n)
    (b p : Fin n) :
    (macroWord ring b p).length = n - p.val := by
  simp only [macroWord, prefixWord, List.length_append,
    walkWord_length, List.length_cons, List.length_nil]
  have hn := ring.hn
  have hp := p.isLt
  omega

private theorem rawRun_append_local {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simpa only [List.cons_append, rawRun] using
        ih ((protocol k hk).step ring C e)

/-- The valid order consequence is non-strict: p may be the leader. -/
theorem leader_cut_le_of_unshielded {n k : Nat}
    (ring : DirectedRing n) (C : Fin n → State k)
    (b l p : Fin n) (hl : (C l).leader = true)
    (hs : ¬ Shielded (cutView ring b C) p) :
    (cutCoord ring b l).val ≤ p.val := by
  by_cases hle : (cutCoord ring b l).val ≤ p.val
  · exact hle
  · exfalso
    apply hs
    refine ⟨cutCoord ring b l, by omega, ?_⟩
    simpa [cutView] using hl

/-- Actual follower service, including the responder-bullet branch. -/
private theorem follower_service {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hf : (C (ring.rightNeighbor e)).leader = false)
    (hp : (C e).probe = true) :
    let D := (protocol k hk).step ring C e
    (D e).probe = false ∧
      (D (ring.rightNeighbor e)).probe = true ∧
      (∀ i : Fin n, (D i).leader = (C i).leader) ∧
      labelsOf D = labelsOf C := by
  let D := (protocol k hk).step ring C e
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
      (transition hk (C e) (C (ring.rightNeighbor e))).2.probe = true ∧
      (transition hk (C e) (C (ring.rightNeighbor e))).1.leader =
        (C e).leader ∧
      (transition hk (C e) (C (ring.rightNeighbor e))).2.leader =
        (C (ring.rightNeighbor e)).leader := by
    rw [transition_of_nonbarrier hk _ _ hnb]
    cases hb : (C (ring.rightNeighbor e)).bullet <;>
      simp [nonBarrierStep, hf, hp, hb]
  have hne := rightNeighbor_ne_self ring hn2 e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [D, PopulationProtocol.step, protocol] using hlocal.1
  · simpa [D, PopulationProtocol.step, protocol, hne] using hlocal.2.1
  · exact step_leaders_eq_of_local hk ring hn2 C e
      hlocal.2.2.1 hlocal.2.2.2
  · exact labelsOf_step_eq_self_of_not_ready hk ring C e
      (not_advanceReady_of_nonbarrier hk ring C e hnb)

/-- A selected unshielded non-tail probe really moves one site forward.
The barrier and all leader bits stay fixed. No uniqueness assumption is needed.
-/
theorem forward_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hp : (cutView ring b C p).probe = true)
    (hs : ¬ Shielded (cutView ring b C) p)
    (hnt : p ≠ tailCoord ring) :
    let e := cutPos ring b p
    let D := (protocol k hk).step ring C e
    ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) ∧
      OneBarrierAt hk ring D b ∧
      (∀ i : Fin n, (D i).leader = (C i).leader) ∧
      (D e).probe = false ∧
      (cutView ring b D (ring.rightNeighbor p)).probe = true ∧
      ¬ Shielded (cutView ring b D) (ring.rightNeighbor p) := by
  let e := cutPos ring b p
  let D := (protocol k hk).step ring C e
  have heb : e ≠ b := by
    intro he
    apply hnt
    apply cutPos_injective ring b
    change e = cutPos ring b (tailCoord ring)
    rw [cutPos_tailCoord]
    exact he
  have hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    exact heb ((hB e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h))
  have hval := rightNeighbor_val_of_ne_tail ring p hnt
  have hf : (C (ring.rightNeighbor e)).leader = false := by
    cases hbit : (C (ring.rightNeighbor e)).leader with
    | false => rfl
    | true =>
        exfalso
        apply hs
        refine ⟨ring.rightNeighbor p, ?_, ?_⟩
        · rw [hval]
          omega
        · change (C (cutPos ring b (ring.rightNeighbor p))).leader = true
          rw [cutPos_rightNeighbor]
          exact hbit
  have hpp : (C e).probe = true := hp
  obtain ⟨hclear, hmove, hleaders, hlabels⟩ :=
    follower_service hk ring hn2 C e hnb hf hpp
  have hBD : OneBarrierAt hk ring D b := by
    intro i
    change BarrierAt hk ring (labelsOf D) i ↔ i = b
    rw [hlabels]
    exact hB i
  refine ⟨hnb, hBD, hleaders, hclear, ?_, ?_⟩
  · change (D (cutPos ring b (ring.rightNeighbor p))).probe = true
    rw [cutPos_rightNeighbor]
    exact hmove
  · rintro ⟨a, hpa, ha⟩
    apply hs
    refine ⟨a, ?_, ?_⟩
    · rw [hval] at hpa
      omega
    · change (C (cutPos ring b a)).leader = true
      change (D (cutPos ring b a)).leader = true at ha
      rw [hleaders] at ha
      exact ha

/-- Induction over the exact number of nonbarrier services before the tail. -/
theorem chase_prefix {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (b : Fin n) (m : Nat) :
    ∀ (C : Fin n → State k) (p : Fin n),
      OneBarrierAt hk ring C b →
      (cutView ring b C p).probe = true →
      ¬ Shielded (cutView ring b C) p →
      p.val + m = n - 1 →
      let w := walkWord ring (cutPos ring b p) m
      let D := rawRun hk ring C w
      CurrentNonbarrierWord hk ring C w ∧
        OneBarrierAt hk ring D b ∧
        (∀ i : Fin n, (D i).leader = (C i).leader) ∧
        (D b).probe = true := by
  induction m with
  | zero =>
      intro C p hB hp hs hd
      have hpt : p = tailCoord ring := by
        apply Fin.ext
        change p.val = n - 1
        omega
      have hpb : (C b).probe = true := by
        simpa [cutView, hpt] using hp
      exact ⟨trivial, hB, fun _ => rfl, hpb⟩
  | succ m ih =>
      intro C p hB hp hs hd
      have hnt : p ≠ tailCoord ring := by
        intro hpt
        have hv : p.val = n - 1 := congrArg Fin.val hpt
        omega
      let e := cutPos ring b p
      let D1 := (protocol k hk).step ring C e
      obtain ⟨hnb, hB1, hL1, hclear, hp1, hs1⟩ :=
        forward_step hk ring hn2 C b p hB hp hs hnt
      have hd1 : (ring.rightNeighbor p).val + m = n - 1 := by
        rw [rightNeighbor_val_of_ne_tail ring p hnt]
        omega
      have hh := ih D1 (ring.rightNeighbor p) hB1 hp1 hs1 hd1
      rw [cutPos_rightNeighbor] at hh
      obtain ⟨hw, hBF, hLF, hPB⟩ := hh
      refine ⟨⟨hnb, hw⟩, hBF, ?_, hPB⟩
      intro i
      exact (hLF i).trans (hL1 i)

private theorem leaderCount_pos_of_witness {n k : Nat}
    (X : Fin n → State k) (l : Fin n)
    (hl : (X l).leader = true) :
    1 ≤ leaderCount X := by
  let erased : Fin n → Bool :=
    fun i => if i = l then false else (X i).leader
  have hdrop := bitCount_single_drop
    (fun i => (X i).leader) erased l hl
    (by simp [erased])
    (by
      intro i hi
      simp [erased, hi])
  change bitCount erased + 1 = leaderCount X at hdrop
  omega

/-- Exact final barrier hit: birth a second leader or strictly lose danger.
The named leader need not be unique for this local result.
-/
theorem tail_probe_exit {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hl : (C l).leader = true)
    (hp : (C b).probe = true) :
    let D := (protocol k hk).step ring C b
    let b' := if AdvanceReady hk ring C b then ring.rightNeighbor b else b
    OneBarrierAt hk ring D b' ∧
      (MultipleLeaders D ∨ PhiAt ring b' D < PhiAt ring b C) := by
  have hn2 : 1 < n := by omega
  let D := (protocol k hk).step ring C b
  let b' := if AdvanceReady hk ring C b then ring.rightNeighbor b else b
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 ((hB b).2 rfl)
  have hne := rightNeighbor_ne_self ring hn2 b
  have hlocal :
      (transition hk (C b) (C (ring.rightNeighbor b))).1.leader = true ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).1.probe = false ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).2.leader =
        (C (ring.rightNeighbor b)).leader := by
    rw [transition_of_barrier hk _ _ hbar]
    cases hphase : (C b).phase <;>
      cases hpr : (C (ring.rightNeighbor b)).probe <;>
      cases hll : (C (ring.rightNeighbor b)).leader <;>
      simp [barrierStep, probeHitsBarrier, hp, hphase, hpr, hll]
  have hDb : (D b).leader = true := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.1
  have hDp : (D b).probe = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
  have hother : ∀ i : Fin n, i ≠ b → (D i).leader = (C i).leader := by
    intro i hib
    by_cases hir : i = ring.rightNeighbor b
    · subst i
      simpa [D, PopulationProtocol.step, protocol, hne] using hlocal.2.2
    · simp [D, PopulationProtocol.step, protocol, hib, hir]
  have hBD : OneBarrierAt hk ring D b' := by
    dsimp only [D, b']
    exact oneBarrierAt_step hk ring hn2 C b b hnd hB
  refine ⟨hBD, ?_⟩
  by_cases hbl : b = l
  · subst l
    have hleaders : ∀ i : Fin n, (D i).leader = (C i).leader := by
      intro i
      by_cases hib : i = b
      · subst i
        exact hDb.trans hl.symm
      · exact hother i hib
    have hcount :
        leaderCount (cutView ring b D) = leaderCount (cutView ring b C) :=
      leaderCount_eq_of_leaders_eq
        (cutView ring b C) (cutView ring b D)
        (fun i => hleaders (cutPos ring b i))
    have hOldDanger : Dangerous (cutView ring b C) :=
      dangerous_of_tail_probe ring (cutView ring b C)
        (by simpa [cutView] using hp)
    have hOldCutSafe : ¬ Dangerous (cutView ring b D) :=
      not_dangerous_of_tail_leader ring (cutView ring b D)
        (by simpa [cutView] using hDb)
        (by simpa [cutView] using hDp)
    have hcount' :
        leaderCount (cutView ring b' D) = leaderCount (cutView ring b C) := by
      dsimp only [b']
      by_cases hr : AdvanceReady hk ring C b
      · rw [if_pos hr]
        let DF : Fin n → State k :=
          fun i => ((protocol k hk).step ring C b) i
        change leaderCount
          (cutView ring (ring.rightNeighbor b) DF) =
          leaderCount (cutView ring b C)
        have hcv := cutView_nextBarrier ring b DF
        rw [hcv, leaderCount_rotateCut]
        simpa [DF, D] using hcount
      · rw [if_neg hr]
        exact hcount
    have hSafe : ¬ Dangerous (cutView ring b' D) := by
      dsimp only [b']
      by_cases hr : AdvanceReady hk ring C b
      · rw [if_pos hr]
        let DF : Fin n → State k :=
          fun i => ((protocol k hk).step ring C b) i
        change ¬ Dangerous
          (cutView ring (ring.rightNeighbor b) DF)
        have hcv := cutView_nextBarrier ring b DF
        rw [hcv]
        apply not_dangerous_rotate_of_head_probe_free ring (cutView ring b D)
        · have hresp : (D (ring.rightNeighbor b)).probe = false := by
            simp only [D, PopulationProtocol.step, protocol,
              if_neg hne, if_pos rfl]
            rw [transition_of_barrier hk _ _ hbar]
            rw [barrierStep_phase_one_probe_free hk _ _ hr.2.1 hr.2.2]
            exact hr.2.2
          simpa [cutView] using hresp
        · exact hOldCutSafe
      · rw [if_neg hr]
        exact hOldCutSafe
    have hpos := leaderCount_pos_of_witness
      (cutView ring b C) (tailCoord ring)
      (by simpa [cutView] using hl)
    right
    change Phi (cutView ring b' D) < Phi (cutView ring b C)
    simp only [Phi, dangerBit, if_pos hOldDanger, if_neg hSafe, hcount']
    omega
  · left
    exact ⟨b, l, hbl, hDb, (hother l (Ne.symm hbl)).trans hl⟩

/-- Correctness of the specified deterministic word for every dangerous witness.
Only existence of the named leader is used; uniqueness is a stronger input.
-/
theorem dangerous_probe_macro {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hL : (C l).leader = true)
    (hp : (cutView ring b C p).probe = true)
    (hs : ¬ Shielded (cutView ring b C) p) :
    let D := rawRun hk ring C (macroWord ring b p)
    let b' := macroBarrier hk ring C b p
    OneBarrierAt hk ring D b' ∧
      (MultipleLeaders D ∨ PhiAt ring b' D < PhiAt ring b C) := by
  have hn2 : 1 < n := by omega
  let W := prefixWord ring b p
  let E := rawRun hk ring C W
  have hd : p.val + (n - 1 - p.val) = n - 1 := by
    have hpLt := p.isLt
    omega
  have hprep := chase_prefix hk ring hn2 b (n - 1 - p.val)
    C p hB hp hs hd
  change CurrentNonbarrierWord hk ring C W ∧
    OneBarrierAt hk ring E b ∧
    (∀ i : Fin n, (E i).leader = (C i).leader) ∧
    (E b).probe = true at hprep
  obtain ⟨hword, hBE, hLE, hPE⟩ := hprep
  have hDangerC : Dangerous (cutView ring b C) := ⟨p, hp, hs⟩
  have hDangerE : Dangerous (cutView ring b E) :=
    dangerous_of_tail_probe ring (cutView ring b E)
      (by simpa [cutView] using hPE)
  have hcount :
      leaderCount (cutView ring b E) = leaderCount (cutView ring b C) :=
    leaderCount_eq_of_leaders_eq
      (cutView ring b C) (cutView ring b E)
      (fun i => hLE (cutPos ring b i))
  have hPhiEq : PhiAt ring b E = PhiAt ring b C := by
    change Phi (cutView ring b E) = Phi (cutView ring b C)
    simp only [Phi, dangerBit, if_pos hDangerE, if_pos hDangerC, hcount]
  have hrun :
      rawRun hk ring C (macroWord ring b p) =
        (protocol k hk).step ring E b := by
    rw [macroWord, rawRun_append_local]
    rfl
  have hExit := tail_probe_exit hk ring hn3 hnd E b l hBE
    ((hLE l).trans hL) hPE
  obtain ⟨hBFinal, hOut⟩ := hExit
  change
    OneBarrierAt hk ring (rawRun hk ring C (macroWord ring b p))
      (if AdvanceReady hk ring E b then ring.rightNeighbor b else b) ∧
    (MultipleLeaders (rawRun hk ring C (macroWord ring b p)) ∨
      PhiAt ring
        (if AdvanceReady hk ring E b then ring.rightNeighbor b else b)
        (rawRun hk ring C (macroWord ring b p)) < PhiAt ring b C)
  rw [hrun]
  refine ⟨hBFinal, ?_⟩
  rcases hOut with hmulti | hlt
  · exact Or.inl hmulti
  · right
    rw [← hPhiEq]
    exact hlt

/-- The requested connector, with a nonempty word of length at most n.
The Clean branch is included by weakening a stronger two-way conclusion.
-/
theorem uniqueLeader_dangerous_macro {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l)
    (hD : Dangerous (cutView ring b C)) :
    ∃ w : List (Fin n),
      0 < w.length ∧ w.length ≤ n ∧
      ∃ b' : Fin n,
        OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
        ((∃ l' : Fin n, CleanAt hk ring (rawRun hk ring C w) b' l') ∨
          MultipleLeaders (rawRun hk ring C w) ∨
          PhiAt ring b' (rawRun hk ring C w) < PhiAt ring b C) := by
  obtain ⟨p, hp, hs⟩ := hD
  let w := macroWord ring b p
  let b' := macroBarrier hk ring C b p
  have hm := dangerous_probe_macro hk ring hn3 hnd C b l p hB hu.1 hp hs
  have hlen : w.length = n - p.val := macroWord_length ring b p
  refine ⟨w, ?_, ?_, b', hm.1, Or.inr hm.2⟩
  · have hpLt := p.isLt
    omega
  · omega

end AAFJPK.OriginalDangerousProbeChase
