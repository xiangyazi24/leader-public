import Leader.Wu.Safety.NoCheckBirthBoundaryFrames

/-!
# Condition-1 preservation without a CHECK provenance premise

Removing CHECK as a leader writer eliminates the comparison-history premise
from Wu's unique-leader closedness argument. This file proves the resulting
source-level configuration theorem. The local interface first isolates the two
fields needed for old-leader survival at Algorithm 15—responder-label framing
and peaceful bullet/shield framing—then discharges both from `OutputSafeConfig`
using the structural prefix frames.

This proves condition 1 for the explicitly named source-shaped repair, not full
five-condition closedness and not literal P_PLL. Conditions 2–5 and the exact
lift from this source-level accounting to the finite authorized/timer carrier
remain separate obligations.
-/

namespace PPLLNoCheckBirthConditionOne

open PPLL PPLLVerify PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthBoundaryFrames

/-- The exact pre-Algorithm-15 pair for one source-level repaired edge. -/
def noCheckBoundaryPair (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :=
  noCheckBirthBeforeEliminate hψ κ (C e) (C (ring.rightNeighbor e))

/-- Exact factored form of the condition-1 boundary pair. -/
theorem noCheckBoundaryPair_eq (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :
    noCheckBoundaryPair hψ κ ring C e =
      noCheckBirthBeforeEliminate hψ κ (C e) (C (ring.rightNeighbor e)) := by
  rfl

/-- Intermediate interface isolating the two old-leader survival facts at the
named suffix boundary. Both fields are constructed below from `OutputSafeConfig`;
leader-pair framing is already unconditional. -/
structure NoCheckConditionOneBoundary
    (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop where
  responder_label : ∀ e,
    (noCheckBoundaryPair hψ κ ring C e).2.label =
      (C (ring.rightNeighbor e)).label
  initiator_no_kill : ∀ e,
    (C e).leader = true →
      ¬((noCheckBoundaryPair hψ κ ring C e).2.bullet = ⟨2, by omega⟩ ∧
        (noCheckBoundaryPair hψ κ ring C e).1.shield = false)

/-- Intermediate peaceful-bullet interface after responder-label framing. It
is inhabited below for every `OutputSafeConfig`. -/
def NoCheckPeaceBoundary
    (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e, (C e).leader = true →
    ¬((noCheckBoundaryPair hψ κ ring C e).2.bullet = ⟨2, by omega⟩ ∧
      (noCheckBoundaryPair hψ κ ring C e).1.shield = false)

attribute [local irreducible] noCheckBirthBeforeEliminate

/-- OutputSafe's peaceful-live-bullet invariant discharges the final
ELIMINATE_LEADERS boundary fact. The complete prefix preserves the initiator
shield and responder bullet exactly, so the unique leader identified by a
peaceful incoming bullet must be the shielded initiator itself. -/
theorem noCheckPeaceBoundary_of_paperSafe
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C) :
    NoCheckPeaceBoundary hψ κ ring C := by
  intro e hleader hbad
  let j := ring.rightNeighbor e
  let q := noCheckBoundaryPair hψ κ ring C e
  have hq : q = noCheckBirthBeforeEliminate hψ κ (C e) (C j) :=
    noCheckBoundaryPair_eq hψ κ ring C e
  have hk0 := noCheckBirthBeforeEliminate_kill_fields hψ κ (C e) (C j)
  have hk : q.1.shield = (C e).shield ∧ q.2.bullet = (C j).bullet := by
    rw [hq]
    exact hk0
  have hbullet : (C j).bullet = ⟨2, by omega⟩ :=
    hk.2.symm.trans hbad.1
  have hnoShield : (C e).shield = false := hk.1.symm.trans hbad.2
  obtain ⟨lp, hlp, huniq⟩ := hSafe.unique_leader
  have heLeader : (C e).isLeader := by
    simpa [AgentState.isLeader] using hleader
  have huniqE : ∀ k, (C k).isLeader → k = e := by
    intro k hkLeader
    exact (huniq k hkLeader).trans (huniq e heLeader).symm
  obtain ⟨_, _, _, hmLeader, hmShield, _, _⟩ :=
    hSafe.no_nonpeaceful_bullet j hbullet
  have hmEq : _ = e := huniqE _ hmLeader
  rw [hmEq] at hmShield
  have hmShieldTrue : (C e).shield = true := by simpa using hmShield
  have hfalse : false = true := hnoShield.symm.trans hmShieldTrue
  exact Bool.noConfusion hfalse

/-- PaperSafe constructs the full condition-1 interface; responder-label
framing and peaceful-bullet survival are now both concrete theorems. -/
theorem noCheckConditionOneBoundary_of_peace
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (hpeace : NoCheckPeaceBoundary hψ κ ring C) :
    NoCheckConditionOneBoundary hψ κ ring C where
  responder_label := by
    intro e
    rw [noCheckBoundaryPair_eq]
    exact noCheckConditionOne_responder_label hψ κ ring C hSafe e
  initiator_no_kill := hpeace

/-- One source-level repaired configuration step through the complete factored
pipeline. -/
def noCheckBirthCoreStep (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (e : Fin n) :
    Fin n → AgentState ψ :=
  let q0 := noCheckBoundaryPair hψ κ ring C e
  let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
  updatePair C e (ring.rightNeighbor e) q

private theorem pPsi_responder_origin_of_noFreeBarrier
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hbarriers : noFreeBarrier hψ ring C)
    (e : Fin n)
    (h : (pPsi hψ (C e) (C (ring.rightNeighbor e))).2.leader = true) :
    (C (ring.rightNeighbor e)).leader = true := by
  by_cases hold : (C (ring.rightNeighbor e)).leader = true
  · exact hold
  · have holdFalse : (C (ring.rightNeighbor e)).leader = false := by
      cases heq : (C (ring.rightNeighbor e)).leader
      · rfl
      · exact (hold heq).elim
    have hbirth := pPsi_new_responder_leader_requires_probe_barrier
      hψ (C e) (C (ring.rightNeighbor e)) h holdFalse
    have hleader := hbarriers e hbirth.2
    simpa [AgentState.isLeader] using hleader

/-- Opaque statement-level wrapper for one repaired source step. -/
def IsNoCheckBirthCoreStep (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C C' : Fin n → AgentState ψ) (e : Fin n) : Prop :=
  C' = noCheckBirthCoreStep hψ κ ring C e

attribute [local irreducible]
  noCheckBirthCoreStep noCheckBirthCoreAfterBeforeEliminate

/-- Global condition-1 assembly from the exact local contracts proved for the
source-shaped pipeline.  This theorem contains no CHECK-history premise: P'_psi
origin, old-leader survival, and zero-label non-migration are the complete
leader interface. -/
theorem uniqueLeader_preserved_from_noCheck_local_contracts
    (hψ : ψ > 0) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) (q : AgentState ψ × AgentState ψ)
    (horiginL : q.1.leader = true →
      (pPsi hψ (C e) (C (ring.rightNeighbor e))).1.leader = true ∨
        (pPsi hψ (C e) (C (ring.rightNeighbor e))).2.leader = true)
    (horiginR : q.2.leader = true →
      (pPsi hψ (C e) (C (ring.rightNeighbor e))).2.leader = true)
    (hsurviveL : (C e).leader = true → q.1.leader = true)
    (hsurviveR : (C (ring.rightNeighbor e)).leader = true →
      q.2.leader = true)
    (hnoMigration : (C e).leader = false →
      (C (ring.rightNeighbor e)).leader = true → q.1.leader = false) :
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) := by
  obtain ⟨lp, hlp, huniq⟩ := hSafe.unique_leader
  let j := ring.rightNeighbor e
  have hne : j ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    simp [j, DirectedRing.rightNeighbor] at hv
    by_cases he : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt he] at hv
      omega
    · have heq : e.val + 1 = n := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  have hpL : (pPsi hψ (C e) (C j)).1.leader = (C e).leader :=
    pPsi_initiator_leader_eq hψ (C e) (C j)
  have hpROrigin : (pPsi hψ (C e) (C j)).2.leader = true →
      (C j).leader = true :=
    pPsi_responder_origin_of_noFreeBarrier hψ ring C
      hSafe.no_free_barrier e
  refine ⟨lp, ?_, ?_⟩
  · by_cases hlpe : lp = e
    · subst lp
      have hCe : (C e).leader = true := by
        simpa [AgentState.isLeader] using hlp
      have hq := hsurviveL hCe
      simpa [updatePair, AgentState.isLeader] using hq
    · by_cases hlpj : lp = j
      · subst lp
        have hCj : (C j).leader = true := by
          simpa [AgentState.isLeader] using hlp
        have hq := hsurviveR hCj
        simpa [updatePair, AgentState.isLeader, j, hlpe, hne] using hq
      · change lp ≠ ring.rightNeighbor e at hlpj
        have hlpLeader : (C lp).leader = true := by
          simpa [AgentState.isLeader] using hlp
        simp [updatePair, AgentState.isLeader, hlpe, hlpj, hlpLeader]
  · intro k hk
    by_cases hke : k = e
    · subst k
      have hout : q.1.leader = true := by
        simpa [updatePair, AgentState.isLeader] using hk
      rcases horiginL hout with hleft | hright
      · have hin : (C e).leader = true := hpL ▸ hleft
        exact huniq e (by simpa [AgentState.isLeader] using hin)
      · have hjLeader : (C j).leader = true := hpROrigin hright
        have hjlp := huniq j (by simpa [AgentState.isLeader] using hjLeader)
        have heFollower : (C e).leader = false := by
          cases heq : (C e).leader
          · rfl
          · have help := huniq e (by simpa [AgentState.isLeader] using heq)
            exact (hne (help.trans hjlp.symm).symm).elim
        have hfalse := hnoMigration heFollower hjLeader
        rw [hfalse] at hout
        contradiction
    · by_cases hkj : k = j
      · subst k
        have hout : q.2.leader = true := by
          simpa [updatePair, AgentState.isLeader, j, hke] using hk
        have hjLeader : (C j).leader = true := hpROrigin (horiginR hout)
        exact huniq j (by simpa [AgentState.isLeader] using hjLeader)
      · change k ≠ ring.rightNeighbor e at hkj
        have hold : (C k).isLeader := by
          simpa [updatePair, hke, hkj] using hk
        exact huniq k hold

/-- Concrete corrected condition-1 wrapper at the named no-CHECK-birth
boundaries.  Explicit `q0/q` equations keep the large transition opaque while
all local contracts are discharged internally. -/
theorem uniqueLeader_preserved_noCheckBirth_boundaries
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (hboundary : NoCheckConditionOneBoundary hψ κ ring C)
    (e : Fin n)
    (q0 q : AgentState ψ × AgentState ψ)
    (hq0 : q0 = noCheckBoundaryPair hψ κ ring C e)
    (hq : q = noCheckBirthCoreAfterBeforeEliminate hψ q0) :
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  have hpre0 := noCheckBirthBeforeEliminate_leaders hψ κ l r
  have hpre : leaderPair q0 = leaderPair (pPsi hψ l r) := by
    rw [hq0]
    exact hpre0
  have horigin0 := noCheckBirthSuffix_origins_of_pPsi_boundary
    hψ l r q0 hpre
  have horiginL : q.1.leader = true →
      (pPsi hψ l r).1.leader = true ∨ (pPsi hψ l r).2.leader = true := by
    rw [hq]
    exact horigin0.1
  have horiginR : q.2.leader = true →
      (pPsi hψ l r).2.leader = true := by
    rw [hq]
    exact horigin0.2
  have hpreL : q0.1.leader = (pPsi hψ l r).1.leader :=
    congrArg Prod.fst hpre
  have hpreR : q0.2.leader = (pPsi hψ l r).2.leader :=
    congrArg Prod.snd hpre
  have hsurviveL : (C e).leader = true → q.1.leader = true := by
    intro hleft
    have hpL : (pPsi hψ l r).1.leader = true := by
      rw [pPsi_initiator_leader_eq hψ l r, hleft]
    have hq0L : q0.1.leader = true := hpreL ▸ hpL
    have hs := noCheckBirthCoreAfterBeforeEliminate_initiator_survives
      hψ q0 hq0L (by
        rw [hq0]
        exact hboundary.initiator_no_kill e hleft)
    rw [hq]
    exact hs
  have hsurviveR : (C (ring.rightNeighbor e)).leader = true →
      q.2.leader = true := by
    intro hright
    have hpR := pPsi_responder_leader_of_true hψ l r hright
    have hq0R : q0.2.leader = true := hpreR ▸ hpR
    have hlabelC := paperSafe_unique_leader_label_zero hψ ring C hSafe
      (ring.rightNeighbor e) (by simpa [AgentState.isLeader] using hright)
    have hq0Label : q0.2.label = ⟨0, hψ⟩ := by
      rw [hq0, hboundary.responder_label e]
      exact hlabelC
    have hs := noCheckBirthCoreAfterBeforeEliminate_responder_survives
      hψ q0 hq0R hq0Label
    rw [hq]
    exact hs
  have hnoMigration : (C e).leader = false →
      (C (ring.rightNeighbor e)).leader = true → q.1.leader = false := by
    intro hleft hright
    have hpL : (pPsi hψ l r).1.leader = false := by
      rw [pPsi_initiator_leader_eq hψ l r, hleft]
    have hq0L : q0.1.leader = false := hpreL ▸ hpL
    have hlabelC := paperSafe_unique_leader_label_zero hψ ring C hSafe
      (ring.rightNeighbor e) (by simpa [AgentState.isLeader] using hright)
    have hq0Label : q0.2.label = ⟨0, hψ⟩ := by
      rw [hq0, hboundary.responder_label e]
      exact hlabelC
    have hn := noCheckBirthCoreAfterBeforeEliminate_no_zero_migration
      hψ q0 hq0L hq0Label
    rw [hq]
    exact hn
  exact uniqueLeader_preserved_from_noCheck_local_contracts
    hψ hn2 ring C hSafe e q horiginL horiginR
      hsurviveL hsurviveR hnoMigration

attribute [local irreducible] noCheckBoundaryPair

/-- Direct named-step form of corrected condition-1 preservation. -/
theorem uniqueLeader_preserved_noCheckBirth
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (hboundary : NoCheckConditionOneBoundary hψ κ ring C)
    (e : Fin n) :
    let q0 := noCheckBoundaryPair hψ κ ring C e
    let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) := by
  let q0 := noCheckBoundaryPair hψ κ ring C e
  let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
  exact uniqueLeader_preserved_noCheckBirth_boundaries
    hψ κ hn2 ring C hSafe hboundary e q0 q rfl rfl

/-- Corrected condition 1 now depends only on one explicit peaceful-bullet
suffix fact, not comparison provenance or label framing. -/
theorem uniqueLeader_preserved_noCheckBirth_of_peace
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (hpeace : NoCheckPeaceBoundary hψ κ ring C)
    (e : Fin n) :
    let q0 := noCheckBoundaryPair hψ κ ring C e
    let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) :=
  uniqueLeader_preserved_noCheckBirth hψ κ hn2 ring C hSafe
    (noCheckConditionOneBoundary_of_peace hψ κ ring C hSafe hpeace) e

/-- **Concrete corrected condition 1.** One full no-CHECK-birth interaction
preserves exactly one leader from every `OutputSafeConfig`, with no comparison
history premise and no explicit boundary assumptions. -/
theorem uniqueLeader_preserved_noCheckBirth_paperSafe
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C) (e : Fin n) :
    let q0 := noCheckBoundaryPair hψ κ ring C e
    let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) :=
  uniqueLeader_preserved_noCheckBirth_of_peace hψ κ hn2 ring C hSafe
    (noCheckPeaceBoundary_of_paperSafe hψ κ ring C hSafe) e

end PPLLNoCheckBirthConditionOne
