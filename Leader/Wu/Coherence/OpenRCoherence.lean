import Leader.Wu.Coherence.LabelPreservation

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31OpenRProof

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2

variable {n ψ κ τ : Nat}

private theorem mod_add_mod_left_openR (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right_openR (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

/-- Local copy of the private algebraic bridge in `R2CoherenceBranches`. -/
private theorem prefixPos_eq_groupPosR2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k =
      R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by
    simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by
    dsimp [a]
    exact Nat.mod_lt _ hn
  have hb : b < n := by
    dsimp [b]
    exact Nat.mod_lt _ hn
  have hA : n ≤ A := by
    dsimp [A]
    omega
  have hLmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by
        rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n =
    (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_openR (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_openR (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by
          omega
        rw [hnum]
  · have hsumGe : n ≤ a + b := by omega
    have hsumSub : a + b - n < n := by omega
    have hLm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hLmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hsumGe
        _ = a + b - n := Nat.mod_eq_of_lt hsumSub
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_openR (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_openR (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by
          omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

private theorem groupPos_label_selfR2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    R2Coherence.groupPos ring C i
        (R2Coherence.raw (C i)).label.val = i := by
  rw [← prefixPos_eq_groupPosR2 ring C i
    (R2Coherence.raw (C i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem groupPos_rightNeighborR2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) :
    ring.rightNeighbor (R2Coherence.groupPos ring C i k) =
      R2Coherence.groupPos ring C i (k + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor R2Coherence.groupPos R2Coherence.fwd
  dsimp only
  rw [mod_add_mod_left_openR]
  congr 1

private theorem prefixPos_eq_groupPosV3
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i : Fin n) (k : Nat) (hk : k ≤ (raw (C i)).label.val) :
    R2Coherence.prefixPos ring (eraseCfgV3 C) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  apply prefixPos_eq_groupPosR2
  change k ≤ (raw (C i)).label.val
  exact hk

private theorem groupPos_label_selfV3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i := by
  have h := groupPos_label_selfR2 ring (eraseCfgV3 C) i
  change
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i at h
  exact h

private theorem groupPos_eq_of_labels
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (D i)).label.val) k =
      R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem prefixPos_eq_of_labels
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem rightNeighbor_injective
    (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

private theorem successor_labels
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem terminal_label
    (u : Cell ψ κ τ) (h : atTerminalB u = true) :
    (raw u).label.val + 1 = ψ := by
  simpa [atTerminalB] using h

/-- Election geometry gives exactly the two label cases exposed by
`passiveEdgeOKV3`. -/
private theorem election_edge_label_cases
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C) (p : Fin n) :
    (raw (C (ring.rightNeighbor p))).label.val = 0 ∨
      (raw (C (ring.rightNeighbor p))).label.val =
        (raw (C p)).label.val + 1 := by
  by_cases hz : (raw (C (ring.rightNeighbor p))).label.val = 0
  · exact Or.inl hz
  · right
    have hRootFalse : atRootB (C (ring.rightNeighbor p)) = false := by
      simp [atRootB, hz]
    have hEdge := hElection p
    unfold passiveEdgeOKV3 at hEdge
    rw [hRootFalse] at hEdge
    have hSucc : successorB (C p) (C (ring.rightNeighbor p)) = true := by
      simpa using hEdge
    exact successor_labels _ _ hSucc

private theorem terminal_next_root
    (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C) (p : Fin n)
    (hTerminal : atTerminalB (C p) = true) :
    (raw (C (ring.rightNeighbor p))).label.val = 0 := by
  rcases election_edge_label_cases ring C hElection p with hz | hs
  · exact hz
  · have ht := terminal_label (C p) hTerminal
    have hlt := (raw (C (ring.rightNeighbor p))).label.isLt
    omega

/-- A terminal-labelled cell cannot be arithmetic offset zero of any
`groupPos` window under `ElectionGeometryV31`. -/
private theorem terminal_not_groupPos_zero
    (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C)
    (i p : Fin n)
    (hp : R2Coherence.groupPos ring (eraseCfgV3 C) i 0 = p)
    (hTerminal : atTerminalB (C p) = true) : False := by
  let L := (raw (C i)).label.val
  have hTerminalVal := terminal_label (C p) hTerminal
  have hSelf0 := groupPos_label_selfV3 ring C i
  have hSelf :
      R2Coherence.groupPos ring (eraseCfgV3 C) i L = i := by
    simpa [L] using hSelf0
  by_cases hL0 : L = 0
  · have hSelf' := hSelf
    rw [hL0] at hSelf'
    have hip : i = p := hSelf'.symm.trans hp
    dsimp [L] at hL0
    rw [← hip] at hTerminalVal
    omega
  · have hLpos : 0 < L := by omega
    have hNext := terminal_next_root h2 ring C hElection p hTerminal
    have hMove0 :=
      groupPos_rightNeighborR2 ring (eraseCfgV3 C) i 0
    rw [hp] at hMove0
    have hMove0' :
        ring.rightNeighbor p =
          R2Coherence.groupPos ring (eraseCfgV3 C) i 1 := by
      simpa using hMove0
    have hBase :
        (raw (C
          (R2Coherence.groupPos ring (eraseCfgV3 C) i 1))).label.val = 0 := by
      rw [← hMove0']
      exact hNext
    have hBound : ∀ t : Nat, t < L →
        (raw (C
          (R2Coherence.groupPos ring (eraseCfgV3 C) i (t + 1)))).label.val ≤ t := by
      intro t
      induction t with
      | zero =>
          intro _
          simpa using hBase
      | succ t ih =>
          intro htL
          have hPrev := ih (by omega)
          have hEdge := election_edge_label_cases ring C hElection
            (R2Coherence.groupPos ring (eraseCfgV3 C) i (t + 1))
          have hMove := groupPos_rightNeighborR2
            ring (eraseCfgV3 C) i (t + 1)
          have hGoal :
              (raw (C
                (R2Coherence.groupPos ring (eraseCfgV3 C) i
                  ((t + 1) + 1)))).label.val ≤ t + 1 := by
            rcases hEdge with hz | hs
            · rw [hMove] at hz
              omega
            · rw [hMove] at hs
              omega
          simpa [Nat.succ_eq_add_one] using hGoal
    have hLast := hBound (L - 1) (by omega)
    have hIdx : L - 1 + 1 = L := by omega
    rw [hIdx, hSelf] at hLast
    omega

/-- This is the boundary-overlap bridge: whenever the
terminal responder occurs in an arithmetic window, that same window contains
its predecessor, i.e. the active `openR` owner. -/
private theorem terminal_window_contains_owner
    (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C)
    (owner i : Fin n) (k : Fin ψ)
    (hTerminal : atTerminalB (C (ring.rightNeighbor owner)) = true)
    (hHit : R2Coherence.groupPos ring (eraseCfgV3 C) i k.val =
      ring.rightNeighbor owner) :
    ∃ ko : Fin ψ,
      R2Coherence.groupPos ring (eraseCfgV3 C) i ko.val = owner := by
  have hk0 : k.val ≠ 0 := by
    intro hk
    have h0 :
        R2Coherence.groupPos ring (eraseCfgV3 C) i 0 =
          ring.rightNeighbor owner := by
      simpa [hk] using hHit
    exact terminal_not_groupPos_zero h2 ring C hElection i
      (ring.rightNeighbor owner) h0 hTerminal
  let ko : Fin ψ := ⟨k.val - 1, by omega⟩
  refine ⟨ko, ?_⟩
  have hMove := groupPos_rightNeighborR2
    ring (eraseCfgV3 C) i (k.val - 1)
  have hIdx : k.val - 1 + 1 = k.val := by omega
  rw [hIdx, hHit] at hMove
  apply rightNeighbor_injective ring
  simpa [ko] using hMove

private theorem bool_false_of_not_true (b : Bool) (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all

private theorem branch_openR_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_openR_eq
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = openRStageV3 l r := by
  rcases branch_openR_conditions hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR⟩
  simp [rowV3, hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR]

private theorem edge_distinct_of_successor
    (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have hSame := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hSucc := successor_labels (C e) (C (ring.rightNeighbor e)) hs
  omega

private theorem openRStageV3_good_states
    (l r : Cell ψ κ τ) (hs : successorB l r = true) :
    (raw (openRStageV3 l r).1).state = .none ∧
      (raw (openRStageV3 l r).2).state = .none := by
  unfold openRStageV3
  rw [if_pos hs]
  dsimp only
  split <;> simp [clearMain, setControl, raw]

private theorem openR_step_good_states
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    (raw (stepV3 hψ h2 ring C e e)).state = .none ∧
      (raw (stepV3 hψ h2 ring C e (ring.rightNeighbor e))).state = .none := by
  have hPair := openRStageV3_good_states
    (C e) (C (ring.rightNeighbor e)) hs
  have hRow := rowV3_openR_eq hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hPair' :
      (raw (rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1).state = .none ∧
      (raw (rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2).state = .none := by
    rw [hRow]
    exact hPair
  have hne := edge_distinct_of_successor C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  constructor
  · simpa [stepV3, protocolV3, PopulationProtocol.step] using hPair'.1
  · simpa [stepV3, protocolV3, PopulationProtocol.step, hrne] using hPair'.2

private theorem openR_step_advance_right_nonOpen
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (ht : atTerminalB (C (ring.rightNeighbor e)) = false) :
    NonOpen
      (eraseCellV3
        (stepV3 hψ h2 ring C e (ring.rightNeighbor e))) := by
  have hRow := rowV3_openR_eq hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hPair :
      NonOpen
        (eraseCellV3
          (rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).2) := by
    rw [hRow]
    simp [openRStageV3, hs, ht, NonOpen, eraseCellV3,
      eraseTokenV3, setControl, clearMain]
  have hne := edge_distinct_of_successor C ring e hs
  have hrne : ring.rightNeighbor e ≠ e := Ne.symm hne
  simpa [stepV3, protocolV3, PopulationProtocol.step, hrne] using hPair

private def erasePairOpenR
    (q : Cell ψ κ τ × Cell ψ κ τ) :
    R2Coherence.Cell ψ κ τ × R2Coherence.Cell ψ κ τ :=
  (eraseCellV3 q.1, eraseCellV3 q.2)

private theorem pairMutation_openR_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR)
    (hs : successorB l r = false) :
    PairQuarantineMutation (eraseCellV3 l) (eraseCellV3 r)
      (erasePairOpenR
        (rowV3 hψ (by decide : 0 < 2) h2 l r)) := by
  rw [rowV3_openR_eq hψ h2 l r hb]
  simp [openRStageV3, hs, PairQuarantineMutation, NonOpen,
    erasePairOpenR, startClosing, setControl, eraseCellV3, eraseTokenV3]

private theorem quarantineMutation_openR_bad
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = false) :
    QuarantineMutation
      (eraseCfgV3 C)
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) := by
  have hPair := pairMutation_openR_bad hψ h2
    (C e) (C (ring.rightNeighbor e)) hb hs
  rcases hPair with ⟨hLM, hRM, hLN, hRN⟩
  intro p
  by_cases hpe : p = e
  · subst p
    simpa [eraseCfgV3, erasePairOpenR, stepV3, protocolV3,
      PopulationProtocol.step] using And.intro hLM hLN
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      simpa [eraseCfgV3, erasePairOpenR, stepV3, protocolV3,
        PopulationProtocol.step, hpe] using And.intro hRM hRN
    · have hSame :
        (((eraseCfgV3 C) p).phys ≠ ((eraseCfgV3 C) p).phys →
            NonOpen ((eraseCfgV3 C) p)) ∧
          (NonOpen ((eraseCfgV3 C) p) →
            NonOpen ((eraseCfgV3 C) p)) :=
        ⟨fun h => (h rfl).elim, fun h => h⟩
      simpa [eraseCfgV3, stepV3, protocolV3,
        PopulationProtocol.step, hpe, hpj] using hSame

private theorem prefixDead_of_nonOpen_groupV3
    (ring : DirectedRing n) (D : FC n ψ κ τ)
    (i : Fin n) (k : Fin ψ)
    (h : NonOpen
      (eraseCellV3
        (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)))) :
    R2Coherence.PrefixDead ring (eraseCfgV3 D) i := by
  unfold R2Coherence.PrefixDead
  refine ⟨k, ?_⟩
  change NonOpen
    (eraseCellV3
      (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)))
  exact h

private theorem intrinsic_of_owner_window
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (owner i : Fin n) (k : Fin ψ)
    (hOwner : OpenROwnerFreshV3 ring C owner)
    (hHit : R2Coherence.groupPos ring (eraseCfgV3 C) i k.val = owner) :
    IntrinsicFreshAtV3 ring C i := by
  have hGroup := hOwner i k hHit
  have hAt := hGroup (raw (C i)).label
  have hSelf := groupPos_label_selfV3 ring C i
  rw [hSelf] at hAt
  exact hAt

private theorem freshComponent_labelV3
    (C : FC n ψ κ τ) (p : Fin n) (k : Nat)
    (h : R2Coherence.freshComponent (eraseCellV3 (C p)) k) :
    (raw (C p)).label.val = k := by
  exact h.1

private theorem openR_advance_coherent
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hCoh : CoherentPrefixesV3 ring C)
    (hOwner : OpenROwnerFreshV3 ring C e)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (ht : atTerminalB (C (ring.rightNeighbor e)) = false) :
    CoherentPrefixesV3 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLabels : ∀ p : Fin n,
      (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using
      (stepV3_labels_eq_or_held hψ h2 ring C e p)
  have hStates := openR_step_good_states hψ h2 ring C e hb hs
  have hStateE : (raw (D e)).state = .none := by
    simpa [D] using hStates.1
  have hStateR :
      (raw (D (ring.rightNeighbor e))).state = .none := by
    simpa [D] using hStates.2
  have hRespNon :
      NonOpen (eraseCellV3 (D (ring.rightNeighbor e))) := by
    simpa [D] using
      openR_step_advance_right_nonOpen hψ h2 ring C e hb hs ht
  change R2Coherence.CoherentPrefixes ring (eraseCfgV3 D)
  intro i hEqD0
  change (raw (D i)).state = .equal at hEqD0
  by_cases hDeadD : R2Coherence.PrefixDead ring (eraseCfgV3 D) i
  · exact Or.inl hDeadD
  have hiE : i ≠ e := by
    intro h
    subst i
    have hx := hEqD0
    rw [hStateE] at hx
    cases hx
  have hiR : i ≠ ring.rightNeighbor e := by
    intro h
    subst i
    have hx := hEqD0
    rw [hStateR] at hx
    cases hx
  have hDi : D i = C i := by
    dsimp [D]
    exact stepV3_other hψ h2 ring C e i hiE hiR
  have hEqC : (raw (C i)).state = .equal := by
    simpa [hDi] using hEqD0
  have hEqC0 :
      (R2Coherence.raw ((eraseCfgV3 C) i)).state = .equal := by
    exact hEqC
  have hFresh :
      ∀ k : Fin ((raw (C i)).label.val + 1),
        R2Coherence.freshComponent
          (eraseCellV3
            (C (R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val))) k.val := by
    rcases hCoh i hEqC0 with hDeadC | hFreshC
    · rcases hDeadC with ⟨kw, hkw⟩
      let p := R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val
      have hNonC : NonOpen (eraseCellV3 (C p)) := by
        change NonOpen
          (eraseCellV3
            (C (R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val))) at hkw
        simpa [p] using hkw
      by_cases hpe : p = e
      · have hHit :
            R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val = e := by
          simpa [p] using hpe
        exact (intrinsic_of_owner_window ring C e i kw hOwner hHit) hEqC
      · by_cases hpr : p = ring.rightNeighbor e
        · have hGP := groupPos_eq_of_labels ring hLabels i kw.val
          have hNonD : NonOpen
              (eraseCellV3
                (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kw.val))) := by
            rw [hGP]
            change NonOpen (eraseCellV3 (D p))
            rw [hpr]
            exact hRespNon
          exact (hDeadD
            (prefixDead_of_nonOpen_groupV3 ring D i kw hNonD)).elim
        · have hDp : D p = C p := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p hpe hpr
          have hGP := groupPos_eq_of_labels ring hLabels i kw.val
          have hNonD : NonOpen
              (eraseCellV3
                (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kw.val))) := by
            rw [hGP]
            simpa [p, hDp] using hNonC
          exact (hDeadD
            (prefixDead_of_nonOpen_groupV3 ring D i kw hNonD)).elim
    · exact hFreshC
  right
  change
    ∀ k : Fin ((raw (D i)).label.val + 1),
      R2Coherence.freshComponent
        (eraseCellV3
          (D (R2Coherence.prefixPos ring (eraseCfgV3 D) i k.val))) k.val
  rw [hLabels i]
  intro k
  have hFreshK := hFresh k
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val
  have hPG := prefixPos_eq_groupPosV3 ring C i k.val (by omega)
  have hLabP : (raw (C p)).label.val = k.val := by
    apply freshComponent_labelV3 C p k.val
    simpa [p] using hFreshK
  by_cases hpe : p = e
  · have hHitE :
        R2Coherence.groupPos ring (eraseCfgV3 C) i k.val = e := by
      rw [← hPG]
      simpa [p] using hpe
    have hSucc := successor_labels
      (C e) (C (ring.rightNeighbor e)) hs
    have hLabE : (raw (C e)).label.val = k.val := by
      simpa [hpe] using hLabP
    have hk1 : k.val + 1 < ψ := by
      have hlt := (raw (C (ring.rightNeighbor e))).label.isLt
      omega
    let k1 : Fin ψ := ⟨k.val + 1, hk1⟩
    have hMove := groupPos_rightNeighborR2
      ring (eraseCfgV3 C) i k.val
    rw [hHitE] at hMove
    have hHitR :
        R2Coherence.groupPos ring (eraseCfgV3 C) i (k.val + 1) =
          ring.rightNeighbor e := hMove.symm
    have hGP := groupPos_eq_of_labels ring hLabels i (k.val + 1)
    have hNonD : NonOpen
        (eraseCellV3
          (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k1.val))) := by
      change NonOpen
        (eraseCellV3
          (D (R2Coherence.groupPos ring (eraseCfgV3 D) i (k.val + 1))))
      rw [hGP, hHitR]
      exact hRespNon
    exact (hDeadD
      (prefixDead_of_nonOpen_groupV3 ring D i k1 hNonD)).elim
  · by_cases hpr : p = ring.rightNeighbor e
    · have hkψ : k.val < ψ := by
        have hiLt := (raw (C i)).label.isLt
        omega
      let kk : Fin ψ := ⟨k.val, hkψ⟩
      have hHitR :
          R2Coherence.groupPos ring (eraseCfgV3 C) i k.val =
            ring.rightNeighbor e := by
        rw [← hPG]
        simpa [p] using hpr
      have hGP := groupPos_eq_of_labels ring hLabels i k.val
      have hNonD : NonOpen
          (eraseCellV3
            (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kk.val))) := by
        change NonOpen
          (eraseCellV3
            (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)))
        rw [hGP, hHitR]
        exact hRespNon
      exact (hDeadD
        (prefixDead_of_nonOpen_groupV3 ring D i kk hNonD)).elim
    · have hDp : D p = C p := by
        dsimp [D]
        exact stepV3_other hψ h2 ring C e p hpe hpr
      have hPP := prefixPos_eq_of_labels ring hLabels i k.val
      rw [hPP]
      change R2Coherence.freshComponent (eraseCellV3 (D p)) k.val
      simpa [hDp] using hFreshK

private theorem openR_terminal_coherent
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hElection : ElectionGeometryV31 ring C)
    (hCoh : CoherentPrefixesV3 ring C)
    (hOwner : OpenROwnerFreshV3 ring C e)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (ht : atTerminalB (C (ring.rightNeighbor e)) = true) :
    CoherentPrefixesV3 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLabels : ∀ p : Fin n,
      (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using
      (stepV3_labels_eq_or_held hψ h2 ring C e p)
  have hStates := openR_step_good_states hψ h2 ring C e hb hs
  have hStateE : (raw (D e)).state = .none := by
    simpa [D] using hStates.1
  have hStateR :
      (raw (D (ring.rightNeighbor e))).state = .none := by
    simpa [D] using hStates.2
  change R2Coherence.CoherentPrefixes ring (eraseCfgV3 D)
  intro i hEqD0
  change (raw (D i)).state = .equal at hEqD0
  by_cases hDeadD : R2Coherence.PrefixDead ring (eraseCfgV3 D) i
  · exact Or.inl hDeadD
  have hiE : i ≠ e := by
    intro h
    subst i
    have hx := hEqD0
    rw [hStateE] at hx
    cases hx
  have hiR : i ≠ ring.rightNeighbor e := by
    intro h
    subst i
    have hx := hEqD0
    rw [hStateR] at hx
    cases hx
  have hDi : D i = C i := by
    dsimp [D]
    exact stepV3_other hψ h2 ring C e i hiE hiR
  have hEqC : (raw (C i)).state = .equal := by
    simpa [hDi] using hEqD0
  have hEqC0 :
      (R2Coherence.raw ((eraseCfgV3 C) i)).state = .equal := by
    exact hEqC
  have hFresh :
      ∀ k : Fin ((raw (C i)).label.val + 1),
        R2Coherence.freshComponent
          (eraseCellV3
            (C (R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val))) k.val := by
    rcases hCoh i hEqC0 with hDeadC | hFreshC
    · rcases hDeadC with ⟨kw, hkw⟩
      let p := R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val
      have hNonC : NonOpen (eraseCellV3 (C p)) := by
        change NonOpen
          (eraseCellV3
            (C (R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val))) at hkw
        simpa [p] using hkw
      by_cases hpe : p = e
      · have hHit :
            R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val = e := by
          simpa [p] using hpe
        exact (intrinsic_of_owner_window ring C e i kw hOwner hHit) hEqC
      · by_cases hpr : p = ring.rightNeighbor e
        · have hHitR :
              R2Coherence.groupPos ring (eraseCfgV3 C) i kw.val =
                ring.rightNeighbor e := by
            simpa [p] using hpr
          obtain ⟨ko, hko⟩ := terminal_window_contains_owner
            h2 ring C hElection e i kw ht hHitR
          exact (intrinsic_of_owner_window ring C e i ko hOwner hko) hEqC
        · have hDp : D p = C p := by
            dsimp [D]
            exact stepV3_other hψ h2 ring C e p hpe hpr
          have hGP := groupPos_eq_of_labels ring hLabels i kw.val
          have hNonD : NonOpen
              (eraseCellV3
                (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kw.val))) := by
            rw [hGP]
            simpa [p, hDp] using hNonC
          exact (hDeadD
            (prefixDead_of_nonOpen_groupV3 ring D i kw hNonD)).elim
    · exact hFreshC
  right
  change
    ∀ k : Fin ((raw (D i)).label.val + 1),
      R2Coherence.freshComponent
        (eraseCellV3
          (D (R2Coherence.prefixPos ring (eraseCfgV3 D) i k.val))) k.val
  rw [hLabels i]
  intro k
  have hFreshK := hFresh k
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val
  have hPG := prefixPos_eq_groupPosV3 ring C i k.val (by omega)
  have hLabP : (raw (C p)).label.val = k.val := by
    apply freshComponent_labelV3 C p k.val
    simpa [p] using hFreshK
  by_cases hpe : p = e
  · have hHitE :
        R2Coherence.groupPos ring (eraseCfgV3 C) i k.val = e := by
      rw [← hPG]
      simpa [p] using hpe
    have hLabE : (raw (C e)).label.val = k.val := by
      simpa [hpe] using hLabP
    have hSucc := successor_labels
      (C e) (C (ring.rightNeighbor e)) hs
    have hTerm := terminal_label (C (ring.rightNeighbor e)) ht
    have hCases :
        (raw (C i)).label.val = k.val ∨
          (raw (C i)).label.val = k.val + 1 := by
      have hkLe : k.val ≤ (raw (C i)).label.val := by omega
      have hiLt := (raw (C i)).label.isLt
      omega
    rcases hCases with hL | hL
    · have hSelf := groupPos_label_selfV3 ring C i
      rw [hL] at hSelf
      have hie : i = e := hSelf.symm.trans hHitE
      exact (hiE hie).elim
    · have hMove := groupPos_rightNeighborR2
        ring (eraseCfgV3 C) i k.val
      rw [hHitE] at hMove
      have hHitR :
          R2Coherence.groupPos ring (eraseCfgV3 C) i (k.val + 1) =
            ring.rightNeighbor e := hMove.symm
      have hSelf := groupPos_label_selfV3 ring C i
      rw [hL] at hSelf
      have hir : i = ring.rightNeighbor e := hSelf.symm.trans hHitR
      exact (hiR hir).elim
  · by_cases hpr : p = ring.rightNeighbor e
    · have hHitR :
          R2Coherence.groupPos ring (eraseCfgV3 C) i k.val =
            ring.rightNeighbor e := by
        rw [← hPG]
        simpa [p] using hpr
      have hLabR :
          (raw (C (ring.rightNeighbor e))).label.val = k.val := by
        simpa [hpr] using hLabP
      have hTerm := terminal_label (C (ring.rightNeighbor e)) ht
      have hL : (raw (C i)).label.val = k.val := by
        have hkLe : k.val ≤ (raw (C i)).label.val := by omega
        have hiLt := (raw (C i)).label.isLt
        omega
      have hSelf := groupPos_label_selfV3 ring C i
      rw [hL] at hSelf
      have hir : i = ring.rightNeighbor e := hSelf.symm.trans hHitR
      exact (hiR hir).elim
    · have hDp : D p = C p := by
        dsimp [D]
        exact stepV3_other hψ h2 ring C e p hpe hpr
      have hPP := prefixPos_eq_of_labels ring hLabels i k.val
      rw [hPP]
      change R2Coherence.freshComponent (eraseCellV3 (D p)) k.val
      simpa [hDp] using hFreshK

/-- The ninth V3.1 coherence branch.  Soundness is automatic from the
future-closed controller invariant; the physical proof above discharges the
only missing CHECK/ID case. -/
theorem openR_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BranchCoherenceObligationV31 (κ := κ) (τ := τ)
      hψ h2 ring .openR := by
  intro C e hClosed hb
  rcases hClosed with ⟨hElection, hCoh, hSound⟩
  have hShape := controllerSoundV3_shape hψ h2 ring C hSound
  rcases branch_openR_conditions hψ h2
    (C e) (C (ring.rightNeighbor e)) hb with
    ⟨_, _, _, _, _, hTok⟩
  have hOwner : OpenROwnerFreshV3 ring C e :=
    (hShape.2.2.2 e hTok).2
  constructor
  · cases hs : successorB (C e) (C (ring.rightNeighbor e)) with
    | false =>
        have hMut := quarantineMutation_openR_bad
          hψ h2 ring C e hb hs
        change R2Coherence.CoherentPrefixes ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e))
        exact coherentPrefixes_of_quarantineMutation ring hMut hCoh
    | true =>
        cases ht : atTerminalB (C (ring.rightNeighbor e)) with
        | false =>
            exact openR_advance_coherent
              hψ h2 ring C e hCoh hOwner hb hs ht
        | true =>
            exact openR_terminal_coherent
              hψ h2 ring C e hElection hCoh hOwner hb hs ht
  · exact controllerSoundV3_step hψ h2 ring C e hSound

end R2CoherenceV31OpenRProof
