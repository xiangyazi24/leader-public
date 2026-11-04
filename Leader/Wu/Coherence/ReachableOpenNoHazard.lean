import Leader.Wu.Coherence.ReachableSweep
import Leader.Wu.Coherence.OpenNoHazardFromChainOrigin

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenNoHazard

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31OpenNoHazardClose
open R2NewEqualLocal

variable {n ψ κ τ : Nat}

private theorem bool_false_of_not_true_reach
    (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> simp_all

private theorem branch_openNoHazard_conditions_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false) := by
  unfold branchAtV3 at hb
  by_cases hSeek : r.ctl.tok = .seek
  · rw [if_pos hSeek] at hb
    cases hb
  · rw [if_neg hSeek] at hb
    by_cases hSweep : l.ctl.tok = .sweep
    · rw [if_pos hSweep] at hb
      cases hb
    · rw [if_neg hSweep] at hb
      by_cases hCommit : r.ctl.tok = .commit
      · rw [if_pos hCommit] at hb
        cases hb
      · rw [if_neg hCommit] at hb
        by_cases hRelease : l.ctl.tok = .release
        · rw [if_pos hRelease] at hb
          cases hb
        · rw [if_neg hRelease] at hb
          by_cases hScrub : r.ctl.tok = .scrubL
          · rw [if_pos hScrub] at hb
            cases hb
          · rw [if_neg hScrub] at hb
            by_cases hOpenR : l.ctl.tok = .openR
            · rw [if_pos hOpenR] at hb
              cases hb
            · rw [if_neg hOpenR] at hb
              by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
              · rw [if_pos hNone] at hb
                by_cases hSealed :
                    l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed
                · rw [if_pos hSealed] at hb
                  cases hb
                · rw [if_neg hSealed] at hb
                  by_cases hOpen :
                      l.ctl.mark = .open ∧ r.ctl.mark = .open
                  · rw [if_pos hOpen] at hb
                    by_cases hHaz :
                        pairHazardV3 l.phys r.phys
                          (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
                          (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = true
                    · simp [hHaz] at hb
                    · exact ⟨hNone.1, hNone.2, hOpen.1, hOpen.2,
                        bool_false_of_not_true_reach _ hHaz⟩
                  · rw [if_neg hOpen] at hb
                    cases hb
              · rw [if_neg hNone] at hb
                cases hb

private theorem pairHazardV3_false_pairWrites_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairWrites l r ql qr = false := by
  cases hw : R2Coherence.pairWrites l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, R2Coherence.pairHazard, hw] at h

private theorem pairHazardV3_false_pairRelabels_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    R2Coherence.pairRelabels l r ql qr = false := by
  cases hr : R2Coherence.pairRelabels l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, R2Coherence.pairHazard, hr] at h

private theorem pairHazardV3_false_pairPaths_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    pairPathChangesV3 l r ql qr = false := by
  cases hp : pairPathChangesV3 l r ql qr with
  | false => rfl
  | true => simp [pairHazardV3, hp] at h

private theorem pairWrites_false_bits_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairWrites l r ql qr = false) :
    l.base.core.core.bit = ql.base.core.core.bit ∧
      r.base.core.core.bit = qr.base.core.core.bit := by
  simpa [R2Coherence.pairWrites, R2Coherence.bitChanged] using h

private theorem pairRelabels_false_labels_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : R2Coherence.pairRelabels l r ql qr = false) :
    l.base.core.core.label = ql.base.core.core.label ∧
      r.base.core.core.label = qr.base.core.core.label := by
  simpa [R2Coherence.pairRelabels, R2Coherence.labelChanged] using h

private theorem pairPaths_false_paths_reach
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairPathChangesV3 l r ql qr = false) :
    l.base.core.core.path = ql.base.core.core.path ∧
      r.base.core.core.path = qr.base.core.core.path := by
  simpa [pairPathChangesV3, pathChangedV3] using h

private theorem proposal_main_frame_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
    R2MainCarrierFrame l.phys r.phys p := by
  rcases branch_openNoHazard_conditions_reach hψ h2 l r hb with
    ⟨_, _, _, _, hHaz⟩
  let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
  have hW := pairHazardV3_false_pairWrites_reach
    l.phys r.phys p.1 p.2 hHaz
  have hR := pairHazardV3_false_pairRelabels_reach
    l.phys r.phys p.1 p.2 hHaz
  have hP := pairHazardV3_false_pairPaths_reach
    l.phys r.phys p.1 p.2 hHaz
  have hBits := pairWrites_false_bits_reach l.phys r.phys p.1 p.2 hW
  have hLabs := pairRelabels_false_labels_reach l.phys r.phys p.1 p.2 hR
  have hPaths := pairPaths_false_paths_reach l.phys r.phys p.1 p.2 hP
  change R2MainCarrierFrame l.phys r.phys p
  unfold R2MainCarrierFrame
  exact ⟨hLabs.1.symm, hBits.1.symm, hPaths.1.symm,
    hLabs.2.symm, hBits.2.symm, hPaths.2.symm⟩

private theorem rowV3_openNoHazard_eq_install_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
    rowV3 hψ (by decide : 0 < 2) h2 l r =
      (install l p.1, install r p.2) := by
  rcases branch_openNoHazard_conditions_reach hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let p := proposalV3 hψ (by decide : 0 < 2) h2 l r
  change rowV3 hψ (by decide : 0 < 2) h2 l r =
    (install l p.1, install r p.2)
  simp [rowV3, ordinaryStageV3, openStageV3,
    hln, hrn, hlo, hro, p, hHaz]

private theorem step_left_eq_proposal_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    (stepV3 hψ h2 ring C e) e = install (C e) p.1 := by
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :
      rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) =
        (install (C e) p.1,
          install (C (ring.rightNeighbor e)) p.2) := by
    simpa [p] using
      (rowV3_openNoHazard_eq_install_reach hψ h2
        (C e) (C (ring.rightNeighbor e)) hb)
  change (stepV3 hψ h2 ring C e) e = install (C e) p.1
  simpa [stepV3, protocolV3, PopulationProtocol.step] using
    congrArg Prod.fst hrow

private theorem step_right_eq_proposal_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let p := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) =
      install (C (ring.rightNeighbor e)) p.2 := by
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow :
      rowV3 hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) =
        (install (C e) p.1,
          install (C (ring.rightNeighbor e)) p.2) := by
    simpa [p] using
      (rowV3_openNoHazard_eq_install_reach hψ h2
        (C e) (C (ring.rightNeighbor e)) hb)
  change (stepV3 hψ h2 ring C e) (ring.rightNeighbor e) =
    install (C (ring.rightNeighbor e)) p.2
  simpa [stepV3, protocolV3, PopulationProtocol.step, hne] using
    congrArg Prod.snd hrow

private theorem prefixPos_eq_of_openFrame_reach
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [(hF i).1]

private theorem groupPos_eq_of_openFrame_reach
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [(hF i).1]

private theorem freshComponent_of_openFrame_reach
    {C D : FC n ψ κ τ} (hF : OpenNoHazardFrameV31 C D)
    (p : Fin n) (k : Nat)
    (h : R2Coherence.freshComponent (eraseCellV3 (C p)) k) :
    R2Coherence.freshComponent (eraseCellV3 (D p)) k := by
  change
    (raw (D p)).label.val = k ∧
      match (raw (D p)).path with
      | .bot => False
      | .some lab b =>
          lab.val = k ∧ b.val = (if (raw (D p)).bit then 1 else 0)
  change
    (raw (C p)).label.val = k ∧
      match (raw (C p)).path with
      | .bot => False
      | .some lab b =>
          lab.val = k ∧ b.val = (if (raw (C p)).bit then 1 else 0) at h
  rcases hF p with ⟨hlab, hbit, hpath, _⟩
  rw [hlab, hbit, hpath]
  exact h

private theorem freshComponent_install_of_own_reach
    (u : Cell ψ κ τ) (p : R2.Cell ψ κ τ)
    (h : R2FreshAtOwnLabel p) :
    R2Coherence.freshComponent (eraseCellV3 (install u p))
      p.base.core.core.label.val := by
  unfold R2FreshAtOwnLabel at h
  change
    p.base.core.core.label.val = p.base.core.core.label.val ∧
      match p.base.core.core.path with
      | .bot => False
      | .some lab b =>
          lab.val = p.base.core.core.label.val ∧
            b.val = (if p.base.core.core.bit then 1 else 0)
  exact ⟨rfl, h⟩

private theorem mod_add_mod_left_reach (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right_reach (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem prefixPos_eq_groupPosR2_reach
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k =
      R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
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
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_reach (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_reach (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by omega
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
        mod_add_mod_left_reach (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using
          (mod_add_mod_right_reach (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

private theorem groupPos_label_selfV3_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i := by
  change
    R2Coherence.groupPos ring (eraseCfgV3 C) i
        (R2Coherence.raw ((eraseCfgV3 C) i)).label.val = i
  rw [← prefixPos_eq_groupPosR2_reach ring (eraseCfgV3 C) i
    (R2Coherence.raw ((eraseCfgV3 C) i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem groupPos_rightNeighborR2_reach
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) :
    ring.rightNeighbor (R2Coherence.groupPos ring C i k) =
      R2Coherence.groupPos ring C i (k + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor R2Coherence.groupPos R2Coherence.fwd
  dsimp only
  rw [mod_add_mod_left_reach]
  congr 1

private theorem rightNeighbor_injective_reach
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

private theorem successor_labels_reach
    (l r : Cell ψ κ τ) (h : successorB l r = true) :
    (raw r).label.val = (raw l).label.val + 1 := by
  simpa [successorB] using h

private theorem election_edge_label_cases_reach
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
    exact successor_labels_reach _ _ hSucc

private theorem groupPos_zero_label_zero_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C) (i : Fin n) :
    (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) i 0))).label.val = 0 := by
  let L := (raw (C i)).label.val
  let a0 :=
    (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) i 0))).label.val
  have hSelf :
      R2Coherence.groupPos ring (eraseCfgV3 C) i L = i := by
    simpa [L] using groupPos_label_selfV3_reach ring C i
  have hInv : ∀ t : Nat, t ≤ L →
      (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) i t))).label.val =
          a0 + t ∨
        (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) i t))).label.val < t := by
    intro t
    induction t with
    | zero =>
        intro _
        left
        simp [a0]
    | succ t ih =>
        intro ht
        have hPrev := ih (by omega)
        have hEdge := election_edge_label_cases_reach ring C hElection
          (R2Coherence.groupPos ring (eraseCfgV3 C) i t)
        have hMove := groupPos_rightNeighborR2_reach
          ring (eraseCfgV3 C) i t
        rcases hEdge with hz | hs
        · right
          rw [hMove] at hz
          rw [hz]
          omega
        · rw [hMove] at hs
          rcases hPrev with hlin | hsmall
          · left
            omega
          · right
            omega
  have hFinal := hInv L (Nat.le_refl L)
  rw [hSelf] at hFinal
  rcases hFinal with hlin | hsmall
  · have ha0 : a0 = 0 := by
      dsimp [L] at hlin
      omega
    simpa [a0] using ha0
  · dsimp [L] at hsmall
    omega

theorem nonroot_window_contains_predecessor_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hElection : ElectionGeometryV31 ring C)
    (i e : Fin n) (k : Fin ψ)
    (hNonroot :
      (raw (C (ring.rightNeighbor e))).label.val ≠ 0)
    (hHit : R2Coherence.groupPos ring (eraseCfgV3 C) i k.val =
      ring.rightNeighbor e) :
    ∃ kp : Fin ψ,
      R2Coherence.groupPos ring (eraseCfgV3 C) i kp.val = e := by
  have hk0 : k.val ≠ 0 := by
    intro hk
    have h0 :
        R2Coherence.groupPos ring (eraseCfgV3 C) i 0 =
          ring.rightNeighbor e := by
      simpa [hk] using hHit
    have hz := groupPos_zero_label_zero_reach ring C hElection i
    rw [h0] at hz
    exact hNonroot hz
  let kp : Fin ψ := ⟨k.val - 1, by omega⟩
  refine ⟨kp, ?_⟩
  change R2Coherence.groupPos ring (eraseCfgV3 C) i (k.val - 1) = e
  have hMove := groupPos_rightNeighborR2_reach
    ring (eraseCfgV3 C) i (k.val - 1)
  have hIdx : k.val - 1 + 1 = k.val := by omega
  rw [hIdx, hHit] at hMove
  exact rightNeighbor_injective_reach ring hMove

theorem back_rightNeighbor_succ_reach
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (ring.rightNeighbor i) (d + 1) =
      R2Coherence.back ring i d := by
  apply Fin.ext
  unfold R2Coherence.back DirectedRing.rightNeighbor
  dsimp only
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hn : 0 < n := ring.hn
    have hn2 : 2 ≤ n := by omega
    have hOne : 1 < n := by omega
    have hdlt : d % n < n := Nat.mod_lt _ ring.hn
    have hdmod : (d + 1) % n = (d % n + 1) % n := by
      calc
        (d + 1) % n = (d % n + 1 % n) % n := Nat.add_mod _ _ _
        _ = (d % n + 1) % n := by rw [Nat.mod_eq_of_lt hOne]
    rw [hdmod]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hnum :
            i.val + 1 + n - (d % n + 1) =
              i.val + n - d % n := by omega
        rw [hnum]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero]
        have hr : i.val + n - d % n = i.val + 1 := by omega
        rw [hr, Nat.mod_eq_of_lt hi]
        have hl : i.val + 1 + n = n + (i.val + 1) := by omega
        rw [hl, Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_mod, Nat.mod_eq_of_lt hi]
    · have hieq : i.val + 1 = n := by omega
      rw [hieq, Nat.mod_self, Nat.zero_add]
      by_cases hd : d % n + 1 < n
      · rw [Nat.mod_eq_of_lt hd]
        have hvlt : n - (d % n + 1) < n := by omega
        rw [Nat.mod_eq_of_lt hvlt]
        have hr :
            i.val + n - d % n =
              n + (n - (d % n + 1)) := by omega
        rw [hr, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hvlt]
      · have hdeq : d % n + 1 = n := by omega
        rw [hdeq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
        have hr : i.val + n - d % n = n := by omega
        rw [hr, Nat.mod_self]

private theorem prefixPos_successor_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (k : Nat) (hk : k ≤ (raw (C e)).label.val) :
    R2Coherence.prefixPos ring (eraseCfgV3 C)
        (ring.rightNeighbor e) k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) e k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring (ring.rightNeighbor e)
        ((raw (C (ring.rightNeighbor e))).label.val - k) =
      R2Coherence.back ring e ((raw (C e)).label.val - k)
  rw [successor_labels_reach (C e) (C (ring.rightNeighbor e)) hs]
  have hsub :
      (raw (C e)).label.val + 1 - k =
        ((raw (C e)).label.val - k) + 1 := by
    omega
  rw [hsub]
  exact back_rightNeighbor_succ_reach ring e
    ((raw (C e)).label.val - k)

private theorem prefixPos_own_r2_reach
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) :
    R2Coherence.prefixPos ring C i
        (R2Coherence.raw (C i)).label.val = i := by
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem freshPrefix_zero_of_own_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hzero : (raw (C i)).label.val = 0)
    (hOwn :
      R2Coherence.freshComponent (eraseCellV3 (C i))
        (raw (C i)).label.val) :
    ∀ k : Fin ((raw (C i)).label.val + 1),
      R2Coherence.freshComponent
        (eraseCellV3
          (C (R2Coherence.prefixPos ring (eraseCfgV3 C) i k.val))) k.val := by
  intro k
  have hk : k.val = (raw (C i)).label.val := by
    have hlt := k.isLt
    omega
  have hp := prefixPos_own_r2_reach ring (eraseCfgV3 C) i
  change
    R2Coherence.prefixPos ring (eraseCfgV3 C) i
        (raw (C i)).label.val = i at hp
  rw [hk, hp]
  exact hOwn

private theorem intrinsicFresh_zero_of_own_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hzero : (raw (C i)).label.val = 0)
    (hOwn :
      R2Coherence.freshComponent (eraseCellV3 (C i))
        (raw (C i)).label.val) :
    IntrinsicFreshAtV3 ring C i := by
  intro _
  exact freshPrefix_zero_of_own_reach ring C i hzero hOwn

private theorem intrinsicFresh_existing_of_openFrame_reach
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (i : Fin n)
    (hOld : IntrinsicFreshAtV3 ring C i)
    (heqC : (raw (C i)).state = .equal) :
    IntrinsicFreshAtV3 ring D i := by
  unfold IntrinsicFreshAtV3 at hOld ⊢
  intro _
  intro k
  have hv :
      (raw (D i)).label.val = (raw (C i)).label.val :=
    congrArg Fin.val (hF i).1
  have hkC : k.val < (raw (C i)).label.val + 1 := by
    calc
      k.val < (raw (D i)).label.val + 1 := k.isLt
      _ = (raw (C i)).label.val + 1 := by rw [hv]
  let kC : Fin ((raw (C i)).label.val + 1) := ⟨k.val, hkC⟩
  have hf := hOld heqC kC
  have hp := prefixPos_eq_of_openFrame_reach ring hF i k.val
  rw [hp]
  exact freshComponent_of_openFrame_reach hF _ _ hf

private theorem intrinsicFresh_successor_ext_reach
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (heqL : (raw (C e)).state = .equal)
    (hLeft : IntrinsicFreshAtV3 ring C e)
    (hOwn :
      R2Coherence.freshComponent
        (eraseCellV3 (C (ring.rightNeighbor e)))
        (raw (C (ring.rightNeighbor e))).label.val) :
    IntrinsicFreshAtV3 ring C (ring.rightNeighbor e) := by
  intro _heqR
  have hfresh := hLeft heqL
  intro k
  have hLab := successor_labels_reach
    (C e) (C (ring.rightNeighbor e)) hs
  by_cases htop :
      k.val = (raw (C (ring.rightNeighbor e))).label.val
  · rw [htop]
    have hp := prefixPos_own_r2_reach ring (eraseCfgV3 C)
      (ring.rightNeighbor e)
    change
      R2Coherence.prefixPos ring (eraseCfgV3 C) (ring.rightNeighbor e)
          (raw (C (ring.rightNeighbor e))).label.val =
        ring.rightNeighbor e at hp
    rw [hp]
    exact hOwn
  · have hkRlt :
        k.val < (raw (C (ring.rightNeighbor e))).label.val + 1 := k.isLt
    have hkR : k.val ≤ (raw (C (ring.rightNeighbor e))).label.val :=
      Nat.le_of_lt_succ hkRlt
    have hkLtR : k.val < (raw (C (ring.rightNeighbor e))).label.val :=
      Nat.lt_of_le_of_ne hkR htop
    have hkL : k.val ≤ (raw (C e)).label.val := by
      omega
    let kL : Fin ((raw (C e)).label.val + 1) :=
      ⟨k.val, Nat.lt_succ_of_le hkL⟩
    have hp := prefixPos_successor_reach ring C e hs k.val hkL
    rw [hp]
    exact hfresh kL

private theorem successor_of_election_nonroot_frame_reach
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hGeom : ElectionGeometryV31 ring C)
    (hF : OpenNoHazardFrameV31 C D) (e : Fin n)
    (hnz : (raw (D (ring.rightNeighbor e))).label.val ≠ 0) :
    successorB (D e) (D (ring.rightNeighbor e)) = true := by
  have hnzC : (raw (C (ring.rightNeighbor e))).label.val ≠ 0 := by
    intro hz
    apply hnz
    have hv := congrArg Fin.val (hF (ring.rightNeighbor e)).1
    exact hv.trans hz
  have hRoot : atRootB (C (ring.rightNeighbor e)) = false := by
    simp [atRootB, hnzC]
  have hEdge := hGeom e
  unfold passiveEdgeOKV3 at hEdge
  rw [hRoot] at hEdge
  have hsC : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa using hEdge
  have hLe := congrArg Fin.val (hF e).1
  have hLr := congrArg Fin.val (hF (ring.rightNeighbor e)).1
  change decide
    ((raw (D (ring.rightNeighbor e))).label.val =
      (raw (D e)).label.val + 1) = true
  change decide
    ((raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1) = true at hsC
  rw [hLr, hLe]
  exact hsC

private theorem owned_site_unchanged_openNoHazard_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hOwned : PhaseOwnedV31 (C p)) :
    stepV3 hψ h2 ring C e p = C p := by
  rcases branch_openNoHazard_conditions_reach hψ h2
      (C e) (C (ring.rightNeighbor e)) hb with
    ⟨hln, hrn, hlo, hro, _⟩
  have hpe : p ≠ e := by
    intro h
    subst p
    unfold PhaseOwnedV31 at hOwned
    rcases hOwned with hm | ht
    · exact hm hlo
    · exact ht hln
  have hpr : p ≠ ring.rightNeighbor e := by
    intro h
    subst p
    unfold PhaseOwnedV31 at hOwned
    rcases hOwned with hm | ht
    · exact hm hro
    · exact ht hrn
  exact stepV3_other hψ h2 ring C e p hpe hpr

private theorem sweptPrefix_frame_openNoHazard_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hF : OpenNoHazardFrameV31 C (stepV3 hψ h2 ring C e))
    (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  let D := stepV3 hψ h2 ring C e
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hv :
      (raw ((stepV3 hψ h2 ring C e) i)).label.val =
        (raw (C i)).label.val :=
    congrArg Fin.val (hF i).1
  have hkC : k.val < (raw (C i)).label.val := by
    calc
      k.val < (raw ((stepV3 hψ h2 ring C e) i)).label.val := k.isLt
      _ = (raw (C i)).label.val := hv
  let kC : Fin (raw (C i)).label.val := ⟨k.val, hkC⟩
  have hPrev := hOld kC
  dsimp only at hPrev
  have hp := groupPos_eq_of_openFrame_reach ring hF i k.val
  rw [hp]
  have hsame := owned_site_unchanged_openNoHazard_reach
    hψ h2 ring C e
    (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val) hb hPrev.2
  simpa [D, hsame] using hPrev

private theorem groupOwned_frame_openNoHazard_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hF : OpenNoHazardFrameV31 C (stepV3 hψ h2 ring C e))
    (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  let D := stepV3 hψ h2 ring C e
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  dsimp only
  have hPrev := hOld k
  dsimp only at hPrev
  have hp := groupPos_eq_of_openFrame_reach ring hF i k.val
  rw [hp]
  have hsame := owned_site_unchanged_openNoHazard_reach
    hψ h2 ring C e
    (R2Coherence.groupPos ring (eraseCfgV3 C) i k.val) hb hPrev.2
  simpa [D, hsame] using hPrev

private theorem groupIntrinsicFresh_openNoHazard_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e j : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hOld : GroupIntrinsicFreshV3 ring C j) :
    GroupIntrinsicFreshV3 ring (stepV3 hψ h2 ring C e) j := by
  let D := stepV3 hψ h2 ring C e
  let p := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  have hMain :
      R2MainCarrierFrame (C e).phys (C (ring.rightNeighbor e)).phys p := by
    simpa [p] using proposal_main_frame_reach hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
  have hMainR2 :
      R2MainCarrierFrame (C e).phys (C (ring.rightNeighbor e)).phys
        (R2.row hψ (by decide : 0 < 2) h2
          (sanitizeReadyPhys (C e).phys)
          (sanitizeReadyPhys (C (ring.rightNeighbor e)).phys)) := by
    simpa [p, proposalV3] using hMain
  have hPair0 := hChain
    (C e).phys (C (ring.rightNeighbor e)).phys hMainR2
  have hPair :
      (p.1.base.core.core.state = .equal →
        (C e).phys.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel p.1 ∧ p.1.base.core.core.label.val = 0) ∧
      (p.2.base.core.core.state = .equal →
        (C (ring.rightNeighbor e)).phys.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel p.2 ∧
          (p.2.base.core.core.label.val = 0 ∨
            p.1.base.core.core.state = .equal)) := by
    simpa [p, proposalV3] using hPair0
  have hDe : D e = install (C e) p.1 := by
    simpa [D, p] using step_left_eq_proposal_reach hψ h2 ring C e hb
  unfold GroupIntrinsicFreshV3 at hOld ⊢
  intro t
  have hPos := groupPos_eq_of_openFrame_reach ring hF j t.val
  rw [hPos]
  let site := R2Coherence.groupPos ring (eraseCfgV3 C) j t.val
  change IntrinsicFreshAtV3 ring D site
  have hOldI : IntrinsicFreshAtV3 ring C site := by
    simpa [site] using hOld t
  unfold IntrinsicFreshAtV3
  intro heqD
  by_cases heqC : (raw (C site)).state = .equal
  · exact (intrinsicFresh_existing_of_openFrame_reach
      ring hF site hOldI heqC) heqD
  · by_cases hse : site = e
    · have heqDe : (raw (D e)).state = .equal := by
        simpa [hse] using heqD
      have heqP1 : p.1.base.core.core.state = .equal := by
        have h := heqDe
        rw [hDe] at h
        simpa [install, raw] using h
      have hneL : (C e).phys.base.core.core.state ≠ .equal := by
        simpa [raw, hse] using heqC
      have hNewL := hPair.1 heqP1 hneL
      have hOwn0 := freshComponent_install_of_own_reach (C e) p.1 hNewL.1
      have hOwnD :
          R2Coherence.freshComponent (eraseCellV3 (D e))
            (raw (D e)).label.val := by
        rw [hDe]
        simpa [install, raw] using hOwn0
      have hzD : (raw (D e)).label.val = 0 := by
        rw [hDe]
        simpa [install, raw] using hNewL.2
      have hpref := freshPrefix_zero_of_own_reach ring D e hzD hOwnD
      rw [hse]
      exact hpref
    · by_cases hsr : site = ring.rightNeighbor e
      · have hneRE : ring.rightNeighbor e ≠ e := by
          intro hre
          apply hse
          exact hsr.trans hre
        have hDr :
            D (ring.rightNeighbor e) =
              install (C (ring.rightNeighbor e)) p.2 := by
          simpa [D, p] using
            step_right_eq_proposal_reach hψ h2 ring C e hneRE hb
        have heqDr : (raw (D (ring.rightNeighbor e))).state = .equal := by
          simpa [hsr] using heqD
        have heqP2 : p.2.base.core.core.state = .equal := by
          have h := heqDr
          rw [hDr] at h
          simpa [install, raw] using h
        have hneR :
            (C (ring.rightNeighbor e)).phys.base.core.core.state ≠ .equal := by
          simpa [raw, hsr] using heqC
        have hNewR := hPair.2 heqP2 hneR
        have hOwnR0 := freshComponent_install_of_own_reach
          (C (ring.rightNeighbor e)) p.2 hNewR.1
        have hOwnR :
            R2Coherence.freshComponent
              (eraseCellV3 (D (ring.rightNeighbor e)))
              (raw (D (ring.rightNeighbor e))).label.val := by
          rw [hDr]
          simpa [install, raw] using hOwnR0
        by_cases hzR : (raw (D (ring.rightNeighbor e))).label.val = 0
        · have hpref := freshPrefix_zero_of_own_reach
            ring D (ring.rightNeighbor e) hzR hOwnR
          rw [hsr]
          exact hpref
        · have heqP1 : p.1.base.core.core.state = .equal := by
            rcases hNewR.2 with hzP | hEq
            · have hzD' :
                  (raw (D (ring.rightNeighbor e))).label.val = 0 := by
                rw [hDr]
                simpa [install, raw] using hzP
              exact (hzR hzD').elim
            · exact hEq
          have heqLD : (raw (D e)).state = .equal := by
            rw [hDe]
            simpa [install, raw] using heqP1
          have hLeftD : IntrinsicFreshAtV3 ring D e := by
            by_cases heqCL : (raw (C e)).state = .equal
            · have hzC :
                  (raw (C (ring.rightNeighbor e))).label.val ≠ 0 := by
                intro hz
                apply hzR
                have hv := congrArg Fin.val (hF (ring.rightNeighbor e)).1
                exact hv.trans hz
              have hHit :
                  R2Coherence.groupPos ring (eraseCfgV3 C) j t.val =
                    ring.rightNeighbor e := by
                simpa [site] using hsr
              obtain ⟨tp, htp⟩ :=
                nonroot_window_contains_predecessor_reach
                  ring C hGeom j e t hzC hHit
              have hPreLeft := hOld tp
              rw [htp] at hPreLeft
              exact intrinsicFresh_existing_of_openFrame_reach
                ring hF e hPreLeft heqCL
            · have hneLP :
                  (C e).phys.base.core.core.state ≠ .equal := by
                simpa [raw] using heqCL
              have hNewL := hPair.1 heqP1 hneLP
              have hOwnL0 :=
                freshComponent_install_of_own_reach (C e) p.1 hNewL.1
              have hOwnL :
                  R2Coherence.freshComponent (eraseCellV3 (D e))
                    (raw (D e)).label.val := by
                rw [hDe]
                simpa [install, raw] using hOwnL0
              have hzL : (raw (D e)).label.val = 0 := by
                rw [hDe]
                simpa [install, raw] using hNewL.2
              exact intrinsicFresh_zero_of_own_reach ring D e hzL hOwnL
          have hsD : successorB (D e) (D (ring.rightNeighbor e)) = true :=
            successor_of_election_nonroot_frame_reach ring hGeom hF e hzR
          have hExt := intrinsicFresh_successor_ext_reach
            ring D e hsD heqLD hLeftD hOwnR
          have hpref := hExt heqDr
          rw [hsr]
          exact hpref
      · have hsame : D site = C site := by
          exact stepV3_other hψ h2 ring C e site hse hsr
        have heqOld : (raw (C site)).state = .equal := by
          rw [← hsame]
          exact heqD
        exact (heqC heqOld).elim

theorem openROwnerFresh_openNoHazard_reach
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hOld : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro j k hHitD
  have hPos := groupPos_eq_of_openFrame_reach ring hF j k.val
  rw [hPos] at hHitD
  have hGroup := hOld j k hHitD
  exact groupIntrinsicFresh_openNoHazard_reach
    hψ h2 ring hChain C e j hGeom hb hGroup

/-- Reachable open/no-hazard induction step.  The phase-owned clauses are
literal frame transport because the served pair is open/none; the openR
intrinsic-freshness clause is the only place that consumes the R2 chain-origin
seam. -/
theorem openNoHazardStep_reachable
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hGeom : ElectionGeometryV31 ring C :=
    electionGeometry_of_quarantineTrace hψ h2 ring C hTrace
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  rcases hFacts with
    ⟨hSweep, hCommit, hSealed, hRelease, hScrub, hOpenR⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hiC := hi
    rw [(hF i).2.2.2] at hiC
    exact sweptPrefix_frame_openNoHazard_reach
      hψ h2 ring C e i hb hF (hSweep i hiC)
  · intro i hi
    have hiC := hi
    rw [(hF i).2.2.2] at hiC
    exact groupOwned_frame_openNoHazard_reach
      hψ h2 ring C e i hb hF (hCommit i hiC)
  · intro i hi
    have hiC := hi
    rw [(hF i).2.2.2] at hiC
    exact groupOwned_frame_openNoHazard_reach
      hψ h2 ring C e i hb hF (hSealed i hiC)
  · intro i hi
    have hiC := hi
    rw [(hF i).2.2.2] at hiC
    rcases hRelease i hiC with ⟨hm, hg⟩
    constructor
    · rw [(hF i).2.2.2]
      exact hm
    · exact groupOwned_frame_openNoHazard_reach
        hψ h2 ring C e i hb hF hg
  · intro i hi
    have hiC := hi
    rw [(hF i).2.2.2] at hiC
    rcases hScrub i hiC with ⟨hm, hz, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [(hF i).2.2.2]
      exact hm
    · intro hzero
      apply hz
      have hv := congrArg Fin.val (hF i).1
      rw [← hv]
      exact hzero
    · exact groupOwned_frame_openNoHazard_reach
        hψ h2 ring C e i hb hF hg
  · intro owner hOwner
    have hOwnerC := hOwner
    rw [(hF owner).2.2.2] at hOwnerC
    rcases hOpenR owner hOwnerC with ⟨hm, hfresh⟩
    constructor
    · rw [(hF owner).2.2.2]
      exact hm
    · exact openROwnerFresh_openNoHazard_reach
        hψ h2 ring hChain C e owner hGeom hb hfresh

end R2CoherenceV31ReachableOpenNoHazard
