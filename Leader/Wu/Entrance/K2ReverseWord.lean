import Leader.Wu.Entrance.WriterProtectionWitness
import Leader.Wu.Entrance.StageLawProducers
import Leader.Wu.Elimination.SinkTwoGapStageCells

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace B6EntranceK2FixedWord

open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2

variable {n psi : Nat}

/-- After the literal reverse-envelope R1 word, every core bullet is zero,
provided the actual R1 execution remains leaderless through every prefix.

The reverse order is the whole point: when edge offset `k` is serviced, site
`k+1` is the responder and ends bullet-zero, and because offsets are processed
in DESCENDING order that site is never touched again. Offset `0` is the only
possible accumulator, and the core cannot be there because
`X.core.J.first = cell ring X.env.I.first (collarWidth psi)` with
`collarWidth psi = psi + 1 >= 1`.

Prefix leaderlessness (`LeaderlessAlong`) rather than merely leaderless
endpoints is required, because `R1LeaderlessK2Agreement` is a one-service
theorem needing both input cells and both output cells to be followers. -/
def K2FixedWordLeaderlessSuccessV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))),
    B6WriterSilentGuarded.LeaderlessAlong
      hpsi h2 ring C (k2DrainWord ring X) →
    CoreAll (fun q : Phys psi psi (16 * psi) => q) X
      (fun q : Phys psi psi (16 * psi) =>
        (B6Sanitation.rawCell q).bullet = 0)
      (runHost
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring (k2DrainWord ring X) C)

end B6EntranceK2FixedWord
namespace B6EntranceK2FixedWord

open PPLL
open B6EntranceV2 B6EntranceV2K2
open B6LocalReverseFill

variable {n psi : Nat}

private def k2CutWord
    (ring : DirectedRing n) (X : Workspace ring psi) (m : Nat) :
    List (Fin n) :=
  (List.range m).reverse.map
    (fun k : Nat => BirthCheckChainR1Ring.cell ring X.env.I.first k)

private theorem k2CutWord_succ
    (ring : DirectedRing n) (X : Workspace ring psi) (m : Nat) :
    k2CutWord ring X (m + 1) =
      BirthCheckChainR1Ring.cell ring X.env.I.first m ::
        k2CutWord ring X m := by
  simp [k2CutWord, List.range_succ]

private theorem leaderlessAlong_head
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : PConfig n (Phys psi psi (16 * psi))) (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w) :
    BirthShortDoneTerminalFirstHit.Leaderless C := by
  cases w with
  | nil => exact h
  | cons e w => exact h.1

private theorem leaderlessAlong_tail
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (e : Fin n) (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong
      hpsi h2 ring C (e :: w)) :
    B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring
      (B9Host.hostStep
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C e) w := by
  rw [B9Host.hostStep_r1_eq_step1
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring C e]
  exact h.2

private theorem env_cell_ne_of_ne
    {ring : DirectedRing n} (X : Workspace ring psi) (a b : Nat)
    (ha : a < X.env.I.size) (hb : b < X.env.I.size)
    (hab : a ≠ b) :
    BirthCheckChainR1Ring.cell ring X.env.I.first a ≠
      BirthCheckChainR1Ring.cell ring X.env.I.first b := by
  intro h
  have hf := B6LocalReverseFill.interval_cells_injective X.env.I
    ⟨a, ha⟩ ⟨b, hb⟩ h
  exact hab (congrArg Fin.val hf)

private theorem k2_responder_eq
    (ring : DirectedRing n) (X : Workspace ring psi) (k : Nat) :
    ring.rightNeighbor
        (BirthCheckChainR1Ring.cell ring X.env.I.first k) =
      BirthCheckChainR1Ring.cell ring X.env.I.first (k + 1) := by
  exact BirthCheckChainR1Ring.right_cell ring X.env.I.first k

private theorem k2_step_other_above
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (k j : Nat) (hk : k + 1 < X.env.I.size)
    (hj : k + 1 < j) (hjI : j < X.env.I.size) :
    B9Host.hostStep
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C
        (BirthCheckChainR1Ring.cell ring X.env.I.first k)
        (BirthCheckChainR1Ring.cell ring X.env.I.first j) =
      C (BirthCheckChainR1Ring.cell ring X.env.I.first j) := by
  apply B9Host.hostStep_other
  · exact env_cell_ne_of_ne X j k hjI (by omega) (by omega)
  · rw [k2_responder_eq ring X k]
    exact env_cell_ne_of_ne X j (k + 1) hjI hk (by omega)

private theorem k2_step_responder_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (k : Nat) (hk : k + 1 < X.env.I.size)
    (hC : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hD : BirthShortDoneTerminalFirstHit.Leaderless
      (B9Host.hostStep
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C
        (BirthCheckChainR1Ring.cell ring X.env.I.first k))) :
    (B6Sanitation.rawCell
      (B9Host.hostStep
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C
        (BirthCheckChainR1Ring.cell ring X.env.I.first k)
        (BirthCheckChainR1Ring.cell ring X.env.I.first (k + 1)))).bullet = 0 := by
  let e := BirthCheckChainR1Ring.cell ring X.env.I.first k
  let r := ring.rightNeighbor e
  let host := B9Host.r1Host
    (kappa := psi) (tau := 16 * psi) hpsi h2
  let q := host.row (C e) (C r)
  have hre : r =
      BirthCheckChainR1Ring.cell ring X.env.I.first (k + 1) := by
    dsimp only [r, e]
    exact k2_responder_eq ring X k
  have hne : r ≠ e := by
    rw [hre]
    exact env_cell_ne_of_ne X (k + 1) k hk (by omega) (by omega)
  have hl : (B6Sanitation.rawCell (C e)).leader = false := by
    change (C e).core.core.leader = false
    exact hC e
  have hr : (B6Sanitation.rawCell (C r)).leader = false := by
    change (C r).core.core.leader = false
    exact hC r
  have hql : (B6Sanitation.rawCell q.1).leader = false := by
    change q.1.core.core.leader = false
    have hh := hD e
    change (B9Host.hostStep host ring C e e).core.core.leader = false at hh
    rw [B9Host.hostStep_left] at hh
    exact hh
  have hqr : (B6Sanitation.rawCell q.2).leader = false := by
    change q.2.core.core.leader = false
    have hh := hD r
    change (B9Host.hostStep host ring C e r).core.core.leader = false at hh
    dsimp only [r] at hne hh
    rw [B9Host.hostStep_right host ring C e hne] at hh
    exact hh
  have hagree :=
    B6EntranceV2K2R1.r1LeaderlessK2Agreement hpsi h2
      (C e) (C r) hl hr hql hqr
  have hleft :
      (K2OutputSafety.signalView
        (ExpiringK2Projection.observeCell (C e))).leader = false := by
    change (B6Sanitation.rawCell (C e)).leader = false
    exact hl
  have hshadow :
      (K2BirthDispatcher.shadowRow
        (ExpiringK2Projection.observeCell (C e))
        (ExpiringK2Projection.observeCell (C r))).2.bullet = 0 := by
    unfold K2BirthDispatcher.shadowRow
    dsimp only
    have hn : ¬
        ((K2OutputSafety.signalView
            (ExpiringK2Projection.observeCell (C e))).leader = true ∧
          (K2OutputSafety.signalView
            (ExpiringK2Projection.observeCell (C r))).leader = true) := by
      intro hh
      simp [hleft] at hh
    rw [if_neg hn]
    exact LDSinkTwoGapAttemptCells.pair_follower_right_zero
      (by decide : 0 < 1)
      (K2OutputSafety.signalView
        (ExpiringK2Projection.observeCell (C e)))
      (K2OutputSafety.signalView
        (ExpiringK2Projection.observeCell (C r))) hleft
  have hb := congrArg
    (fun p : AgentState 1 × AgentState 1 => p.2.bullet)
    hagree
  have hz : (ExpiringK2Projection.observeCell q.2).bullet = 0 :=
    hb.trans hshadow
  rw [← hre]
  rw [B9Host.hostStep_right host ring C e hne]
  change (ExpiringK2Projection.observeCell q.2).bullet = 0
  exact hz

private theorem k2Cut_drain_and_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi) :
    ∀ (m : Nat) (C : PConfig n (Phys psi psi (16 * psi))),
      m ≤ X.env.I.size - 1 →
      B6WriterSilentGuarded.LeaderlessAlong
        hpsi h2 ring C (k2CutWord ring X m) →
      let D := runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring (k2CutWord ring X m) C
      (∀ j : Nat, 1 ≤ j → j ≤ m →
        (B6Sanitation.rawCell
          (D (BirthCheckChainR1Ring.cell ring X.env.I.first j))).bullet = 0) ∧
      (∀ j : Nat, m < j → j < X.env.I.size →
        D (BirthCheckChainR1Ring.cell ring X.env.I.first j) =
          C (BirthCheckChainR1Ring.cell ring X.env.I.first j)) := by
  intro m
  induction m with
  | zero =>
      intro C hm hAlive
      constructor
      · intro j hj1 hj0
        omega
      · intro j hj _
        rfl
  | succ m ih =>
      intro C hm hAlive
      let e := BirthCheckChainR1Ring.cell ring X.env.I.first m
      let host := B9Host.r1Host
        (kappa := psi) (tau := 16 * psi) hpsi h2
      let C1 := B9Host.hostStep host ring C e
      have hword :
          k2CutWord ring X (m + 1) = e :: k2CutWord ring X m := by
        dsimp only [e]
        exact k2CutWord_succ ring X m
      have hAlive' := hAlive
      rw [hword] at hAlive'
      have hTail :
          B6WriterSilentGuarded.LeaderlessAlong
            hpsi h2 ring C1 (k2CutWord ring X m) := by
        dsimp only [C1, host, e]
        exact leaderlessAlong_tail hpsi h2 ring C e
          (k2CutWord ring X m) hAlive'
      have hStart : BirthShortDoneTerminalFirstHit.Leaderless C :=
        leaderlessAlong_head hpsi h2 ring C
          (e :: k2CutWord ring X m) hAlive'
      have hNext : BirthShortDoneTerminalFirstHit.Leaderless C1 :=
        leaderlessAlong_head hpsi h2 ring C1
          (k2CutWord ring X m) hTail
      have hEdge : m + 1 < X.env.I.size := by
        have hs := X.env.I.nonempty
        omega
      have hz :
          (B6Sanitation.rawCell
            (C1 (BirthCheckChainR1Ring.cell
              ring X.env.I.first (m + 1)))).bullet = 0 := by
        dsimp only [C1, host, e]
        exact k2_step_responder_zero hpsi h2 ring X C m hEdge hStart hNext
      have hIH := ih C1 (by omega) hTail
      have hrun :
          runHost host ring (k2CutWord ring X (m + 1)) C =
            runHost host ring (k2CutWord ring X m) C1 := by
        rw [hword]
        rfl
      constructor
      · intro j hj1 hjm
        rw [hrun]
        by_cases hjtop : j = m + 1
        · subst j
          have hf := hIH.2 (m + 1) (by omega) hEdge
          rw [hf]
          exact hz
        · exact hIH.1 j hj1 (by omega)
      · intro j hjm hjI
        rw [hrun]
        have hf := hIH.2 j (by omega) hjI
        rw [hf]
        dsimp only [C1, host, e]
        exact k2_step_other_above hpsi h2 ring X C m j hEdge hjm hjI

private theorem support_eq_true_exists_cell
    {ring : DirectedRing n} (I : Interval ring) (i : Fin n)
    (hi : support I i = true) :
    ∃ k : Nat, k < I.size ∧
      i = BirthCheckChainR1Ring.cell ring I.first k := by
  change (List.range I.size).any
      (fun k : Nat => decide
        (i = BirthCheckChainR1Ring.cell ring I.first k)) = true at hi
  obtain ⟨k, hk, he⟩ := List.any_eq_true.mp hi
  exact ⟨k, List.mem_range.mp hk, of_decide_eq_true he⟩

private theorem mod_add_mod_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

private theorem cell_cell_add
    (ring : DirectedRing n) (s : Fin n) (a b : Nat) :
    BirthCheckChainR1Ring.cell ring
        (BirthCheckChainR1Ring.cell ring s a) b =
      BirthCheckChainR1Ring.cell ring s (a + b) := by
  apply Fin.ext
  simp only [BirthCheckChainR1Ring.cell]
  rw [mod_add_mod_left]
  rw [Nat.add_assoc]

theorem k2FixedWordLeaderlessSuccessV31_holds
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    K2FixedWordLeaderlessSuccessV31 hpsi h2 ring := by
  intro X C hAlive
  have hAlive' :
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C
        (k2CutWord ring X (X.env.I.size - 1)) := by
    simpa [k2CutWord, B6EntranceV2K2.k2DrainWord] using hAlive
  have hSweep := k2Cut_drain_and_frame hpsi h2 ring X
    (X.env.I.size - 1) C (Nat.le_refl _) hAlive'
  unfold B6EntranceV2.CoreAll
  intro i hi
  obtain ⟨j, hj, hij⟩ := support_eq_true_exists_cell X.core.J i hi
  let k := collarWidth psi + j
  have hcell :
      BirthCheckChainR1Ring.cell ring X.core.J.first j =
        BirthCheckChainR1Ring.cell ring X.env.I.first k := by
    dsimp only [k]
    rw [X.core.first_eq]
    exact cell_cell_add ring X.env.I.first (collarWidth psi) j
  have hk1 : 1 ≤ k := by
    dsimp only [k]
    unfold collarWidth
    omega
  have hkEnv : k < X.env.I.size := by
    dsimp only [k]
    rw [X.core.size_eq] at hj
    have hc : 1 ≤ collarWidth psi := by
      unfold collarWidth
      omega
    rw [X.env.size_eq]
    unfold envelopeWidth
    omega
  have hkm : k ≤ X.env.I.size - 1 := by
    omega
  have hz := hSweep.1 k hk1 hkm
  rw [hij, hcell]
  simpa [k2CutWord, B6EntranceV2K2.k2DrainWord] using hz

end B6EntranceK2FixedWord
