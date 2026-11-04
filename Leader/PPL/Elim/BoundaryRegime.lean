import Leader.PPL.Elim.Regimes
import Leader.PPL.Elim.CleanReadyCost
/-!
# LD(736): proved boundary regime b = 1
The missing File-3 clean-live theorem is exposed exactly as a named cost
hypothesis.  Its monitor first reaches CleanReady, then follows the mirrored
File-3 sealed phase, stopping on endpoint deletion or on the first certified
clean live hit.
For the boundary composition, the first stage is File 2 CleanReady on B.
The actual first CleanReady endpoint is retained.  From that endpoint, B has
gap one and is therefore always Ready or Dummy(0) until a tagged deletion.
A clean live hit entering j then deletes j by the literal row-E order:
a Ready responder dummy-fires and becomes unshielded before the incoming live
bullet is tested; a Dummy(0) responder is already unshielded.
The intermediate CRDone target is not forward-closed, so the closed-target
costNumerator_split theorem is not the appropriate composition primitive.
The same-horizon first-hit bind below retains the exact endpoint instead.
-/
namespace PPL.Convergence.LDLocal
set_option autoImplicit false
set_option Elab.async false
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
/-! ## File-3 clean-live monitor -/
inductive LiveHitPrepStage where
  | pre
  | sealed (ph : SectorPhase)
structure LiveHitPrepState (n : Nat) where
  cfg : Config n
  stage : LiveHitPrepStage
/-- A clean live hit is either the one-edge Ready firing when the gap is one,
or the terminal service of an already-moving sealed live bullet. -/
def cleanLiveHitService
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    SectorPhase → Fin n → Prop
  | .ready, e =>
      e = A.left ∧ A.gap = 1
  | .live p, e =>
      e = advance ring A.left p ∧ p + 1 = A.gap
  | .dummy _, _ => False
  | .ret _, _ => False
noncomputable def liveHitPrepStart
    {n : Nat} {ring : DirectedRing n}
    (C : Config n) (A : SectorFrame ring C) :
    LiveHitPrepState n := by
  classical
  exact
    if _h : CleanReady A C then
      { cfg := C, stage := .sealed .ready }
    else
      { cfg := C, stage := .pre }

noncomputable def liveHitPrepStep
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0) :
    LiveHitPrepState n → Fin n → StopNode (LiveHitPrepState n) := by
  classical
  exact fun s e =>
    let D := stepE ring s.cfg e
    if _hdel : EndpointDeleted A D then
      .success
    else
      match s.stage with
      | .pre =>
          if _hclean : CleanReady A D then
            .active { cfg := D, stage := .sealed .ready }
          else
            .active { cfg := D, stage := .pre }
      | .sealed ph =>
          if _hhit : cleanLiveHitService A ph e then
            .success
          else
            .active {
              cfg := D
              stage := .sealed (nextSectorPhase A ph e)
            }

noncomputable def liveHitPrepCostNumerator
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (A : SectorFrame ring C) (T : Nat) : Nat :=
  truncatedActiveCostNumerator
    (liveHitPrepStep ring A)
    (.active (liveHitPrepStart C A)) T
/-- Exact File-3 clean-live cost endpoint from the plan. -/
noncomputable def CleanLiveHitCost : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    (C : Config n) (hPB : PPL.Elim.PB ring C)
    (A : SectorFrame ring C),
    ∀ T,
      liveHitPrepCostNumerator ring C A T ≤
        n ^ T * (n * (6 * A.gap - 1))
/-! ## Boundary phase and geometry -/
def BoundaryBPhase
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n) : Prop :=
  PhaseHolds F.B C .ready ∨
    PhaseHolds F.B C (.dummy 0)
def SameAttackGeometry
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0) : Prop :=
  A.left = F.A.left ∧
    A.right = F.A.right ∧
    A.gap = F.A.gap
def LiveHitSound
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0)
    (s : LiveHitPrepState n) : Prop :=
  TaggedDeleted F s.cfg ∨
    (¬ TaggedDeleted F s.cfg ∧
      BoundaryBPhase F s.cfg ∧
      match s.stage with
      | .pre => CRInteriorFollowers A s.cfg
      | .sealed ph => PhaseHolds A s.cfg ph)
def boundaryAttackFrame
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (D : Config n)
    (htag : ¬ TaggedDeleted F D)
    (hInterior : CRInteriorFollowers F.A D) :
    SectorFrame ring D := {
  left := F.A.left
  right := F.A.right
  gap := F.A.gap
  gap_pos := F.A.gap_pos
  gap_lt_n := F.A.gap_lt_n
  left_ne_right := F.A.left_ne_right
  right_eq := F.A.right_eq
  left_leader := by
    have h := tagged_alive_of_not_deleted F D htag
    rw [F.A_left]
    exact h.1
  right_leader := by
    have h := tagged_alive_of_not_deleted F D htag
    rw [F.A_right]
    exact h.2.1
  interior_follower := by
    intro q hq0 hq
    exact hInterior q hq0 hq
}
/-! ## Literal row-E facts -/
theorem fin3_cases_boundary (x : Fin 3) :
    x = (0 : Fin 3) ∨
      x = (1 : Fin 3) ∨
      x = (2 : Fin 3) := by
  have hx := x.isLt
  have h :
      x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    omega
  rcases h with h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (Fin.ext h))
theorem rightNeighbor_ne_self_boundary
    {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega
theorem stepE_responder_boundary
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepE ring C e (ring.rightNeighbor e) =
      (PPL.Elim.rowE
        (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepE, PopulationProtocol.step,
    PPL.Elim.protocolE, hne, Ne.symm hne]
/-- A pre-existing live bullet, or a source firing live in this row, deletes
a vulnerable leader responder.  If the responder signal is true, lines 53-54
first make it dummy and unshielded; otherwise it is assumed already
unshielded. -/
theorem rowE_kills_vulnerable_boundary
    (l r : PPL.Elim.Cell4)
    (hattack :
      l.bullet = (2 : Fin 3) ∨
        (l.leader = true ∧ l.signalB = true))
    (hrLeader : r.leader = true)
    (hrVulnerable :
      r.signalB = true ∨
        (r.signalB = false ∧ r.shield = false)) :
    (PPL.Elim.rowE l r).2.leader = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_boundary lb with h | h | h <;>
    subst lb <;>
  rcases fin3_cases_boundary rb with h | h | h <;>
    subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]
theorem endpointDeleted_attack_tagged_of_same
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0)
    (C : Config n)
    (hsame : SameAttackGeometry F A)
    (hdel : EndpointDeleted A C) :
    TaggedDeleted F C := by
  rcases hsame with ⟨hleft, hright, _hgap⟩
  rcases hdel with h | h
  · refine .inl ?_
    rw [← F.A_left, ← hleft]
    exact h
  · refine .inr (.inl ?_)
    rw [← F.A_right, ← hright]
    exact h
/-- On a boundary target, every certified clean live hit from A deletes j. -/
theorem boundary_clean_live_hit_deletes_j
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0)
    (C : Config n)
    (hsame : SameAttackGeometry F A)
    (ph : SectorPhase)
    (hA : PhaseHolds A C ph)
    (hB : BoundaryBPhase F C)
    (halive : ¬ TaggedDeleted F C)
    (e : Fin n)
    (hhit : cleanLiveHitService A ph e) :
    TaggedDeleted F (stepE ring C e) := by
  have haliveBits := tagged_alive_of_not_deleted F C halive
  have hJLeader : (C F.j).leader = true :=
    haliveBits.2.1
  have hJVulnerable :
      (C F.j).signalB = true ∨
        ((C F.j).signalB = false ∧
          (C F.j).shield = false) := by
    rcases hB with hready | hdummy
    · refine .inl ?_
      rw [← F.B_left]
      exact hready.2.1
    · refine .inr ⟨?_, ?_⟩
      · have hz :=
          hdummy.2.2.2 0 (Nat.zero_le 0)
        simpa [advance_zero, F.B_left] using hz
      · rw [← F.B_left]
        exact hdummy.2.2.1
  cases ph with
  | ready =>
      rcases hhit with ⟨he, hgap1⟩
      subst e
      have hSourceLeader :
          (C A.left).leader = true := by
        rw [hsame.1, F.A_left]
        exact haliveBits.1
      have hSourceSignal :
          (C A.left).signalB = true :=
        hA.2.1
      have hrn :
          ring.rightNeighbor A.left = F.j := by
        calc
          ring.rightNeighbor A.left =
              advance ring A.left (0 + 1) := by
                simpa using
                  advance_succ_twoLeader ring A.left 0
          _ = advance ring A.left A.gap := by
                rw [hgap1]
          _ = A.right := A.right_eq
          _ = F.A.right := hsame.2.1
          _ = F.j := F.A_right
      have hn2 : 1 < n := by
        have := A.gap_lt_n
        omega
      have hrightLeader :
          (C (ring.rightNeighbor A.left)).leader =
            true := by
        rw [hrn]
        exact hJLeader
      have hrightVulnerable :
          (C (ring.rightNeighbor A.left)).signalB = true ∨
            ((C (ring.rightNeighbor A.left)).signalB = false ∧
              (C (ring.rightNeighbor A.left)).shield = false) := by
        rw [hrn]
        exact hJVulnerable
      have hrow :=
        rowE_kills_vulnerable_boundary
          (C A.left)
          (C (ring.rightNeighbor A.left))
          (.inr ⟨hSourceLeader, hSourceSignal⟩)
          hrightLeader hrightVulnerable
      have hstep :=
        stepE_responder_boundary ring C A.left
          (rightNeighbor_ne_self_boundary ring hn2 A.left)
      have hj :
          (stepE ring C A.left F.j).leader = false := by
        rw [← hrn, hstep]
        exact hrow
      exact .inr (.inl hj)
  | live p =>
      rcases hhit with ⟨he, hterm⟩
      subst e
      have hbullet :
          (C (advance ring A.left p)).bullet =
            (2 : Fin 3) :=
        hA.2.1.2.1
      have hrn :
          ring.rightNeighbor (advance ring A.left p) =
            F.j := by
        calc
          ring.rightNeighbor (advance ring A.left p) =
              advance ring A.left (p + 1) :=
            advance_succ_twoLeader ring A.left p
          _ = advance ring A.left A.gap := by
            rw [hterm]
          _ = A.right := A.right_eq
          _ = F.A.right := hsame.2.1
          _ = F.j := F.A_right
      have hn2 : 1 < n := by
        have hp := A.gap_pos
        have hn := A.gap_lt_n
        omega
      have hrightLeader :
          (C
            (ring.rightNeighbor
              (advance ring A.left p))).leader = true := by
        rw [hrn]
        exact hJLeader
      have hrightVulnerable :
          (C
            (ring.rightNeighbor
              (advance ring A.left p))).signalB = true ∨
            ((C
              (ring.rightNeighbor
                (advance ring A.left p))).signalB = false ∧
              (C
                (ring.rightNeighbor
                  (advance ring A.left p))).shield = false) := by
        rw [hrn]
        exact hJVulnerable
      have hrow :=
        rowE_kills_vulnerable_boundary
          (C (advance ring A.left p))
          (C
            (ring.rightNeighbor
              (advance ring A.left p)))
          (.inl hbullet)
          hrightLeader hrightVulnerable
      have hstep :=
        stepE_responder_boundary
          ring C (advance ring A.left p)
          (rightNeighbor_ne_self_boundary
            ring hn2 (advance ring A.left p))
      have hj :
          (stepE ring C
            (advance ring A.left p) F.j).leader = false := by
        rw [← hrn, hstep]
        exact hrow
      exact .inr (.inl hj)
  | dummy p =>
      simp [cleanLiveHitService] at hhit
  | ret q =>
      simp [cleanLiveHitService] at hhit
/-! ## One-edge target closure -/
theorem boundaryBPhase_step
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : F.b = 1)
    (C : Config n)
    (hphase : BoundaryBPhase F C)
    (halive : ¬ TaggedDeleted F C)
    (e : Fin n) :
    TaggedDeleted F (stepE ring C e) ∨
      BoundaryBPhase F (stepE ring C e) := by
  have hBalive : ¬ EndpointDeleted F.B C := by
    intro hdel
    exact halive
      (endpointDeletedB_tagged_twoLeader F hdel)
  have hBgap : F.B.gap = 1 :=
    F.B_gap.trans hb
  rcases hphase with hready | hdummy
  · rcases
      hSealed ring F.B C .ready
        hready hBalive e with
      hdel | ⟨ph', hholds, htr⟩
    · exact .inl
        (endpointDeletedB_tagged_twoLeader F hdel)
    · rw [htr] at hholds
      by_cases hin : e = sealedIncomingEdge F.B
      · refine .inr (.inr ?_)
        simpa [nextSectorPhase, hin, hBgap] using hholds
      · by_cases hout : e = F.B.left
        · refine .inr (.inl ?_)
          have hleftIncoming :
              F.B.left ≠ sealedIncomingEdge F.B := by
            intro hEq
            have hr := congrArg ring.rightNeighbor hEq
            unfold sealedIncomingEdge at hr
            rw [rightNeighbor_leftNeighbor_twoLeader
              ring F.B.left] at hr
            have hn2 : 1 < n := by
              have hlt := F.B.gap_lt_n
              rw [hBgap] at hlt
              omega
            exact
              (rightNeighbor_ne_self_boundary
                ring hn2 F.B.left) hr
          simpa [nextSectorPhase, hout,
            hleftIncoming, hBgap] using hholds
        · refine .inr (.inl ?_)
          simpa [nextSectorPhase, hin, hout, hBgap] using hholds
  · rcases
      hSealed ring F.B C (.dummy 0)
        hdummy hBalive e with
      hdel | ⟨ph', hholds, htr⟩
    · exact .inl
        (endpointDeletedB_tagged_twoLeader F hdel)
    · rw [htr] at hholds
      by_cases hout : e = F.B.left
      · refine .inr (.inl ?_)
        simpa [nextSectorPhase, advance_zero, hBgap, hout]
          using hholds
      · refine .inr (.inr ?_)
        simpa [nextSectorPhase, advance_zero, hBgap, hout]
          using hholds
/-! ## Soundness of the File-3 live-hit monitor on the boundary -/
theorem liveHitPrep_active_config
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (s s' : LiveHitPrepState n) (e : Fin n)
    (hactive :
      liveHitPrepStep ring A s e = .active s') :
    s'.cfg = stepE ring s.cfg e := by
  classical
  let D := stepE ring s.cfg e
  unfold liveHitPrepStep at hactive
  dsimp only at hactive
  by_cases hdel : EndpointDeleted A D
  · rw [dif_pos hdel] at hactive
    cases hactive
  · rw [dif_neg hdel] at hactive
    cases hstage : s.stage with
    | pre =>
        rw [hstage] at hactive
        dsimp only at hactive
        by_cases hclean : CleanReady A D
        · rw [dif_pos hclean] at hactive
          cases hactive
          rfl
        · rw [dif_neg hclean] at hactive
          cases hactive
          rfl
    | sealed ph =>
        rw [hstage] at hactive
        dsimp only at hactive
        by_cases hhit : cleanLiveHitService A ph e
        · rw [dif_pos hhit] at hactive
          cases hactive
        · rw [dif_neg hhit] at hactive
          cases hactive
          rfl

theorem liveHitPrep_ne_failure
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (s : LiveHitPrepState n) (e : Fin n) :
    liveHitPrepStep ring A s e ≠ .failure := by
  classical
  intro h
  let D := stepE ring s.cfg e
  unfold liveHitPrepStep at h
  dsimp only at h
  by_cases hdel : EndpointDeleted A D
  · rw [dif_pos hdel] at h
    cases h
  · rw [dif_neg hdel] at h
    cases hstage : s.stage with
    | pre =>
        rw [hstage] at h
        dsimp only at h
        by_cases hclean : CleanReady A D
        · rw [dif_pos hclean] at h
          cases h
        · rw [dif_neg hclean] at h
          cases h
    | sealed ph =>
        rw [hstage] at h
        dsimp only at h
        by_cases hhit : cleanLiveHitService A ph e
        · rw [dif_pos hhit] at h
          cases h
        · rw [dif_neg hhit] at h
          cases h

theorem liveHitPrep_success_tagged
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0)
    (hsame : SameAttackGeometry F A)
    (hb : F.b = 1)
    (s : LiveHitPrepState n)
    (e : Fin n)
    (hsound : LiveHitSound F A s)
    (hsuccess :
      liveHitPrepStep ring A s e = .success) :
    TaggedDeleted F (stepE ring s.cfg e) := by
  classical
  unfold LiveHitSound at hsound
  rcases hsound with htag | hgood
  · exact taggedDeleted_step F s.cfg e htag
  · rcases hgood with ⟨hnot, hB, hstageSound⟩
    let D := stepE ring s.cfg e
    unfold liveHitPrepStep at hsuccess
    dsimp only at hsuccess
    cases hstage : s.stage with
    | pre =>
        by_cases hdel : EndpointDeleted A D
        · exact
            endpointDeleted_attack_tagged_of_same
              F A D hsame hdel
        · rw [dif_neg hdel, hstage] at hsuccess
          dsimp only at hsuccess
          by_cases hclean : CleanReady A D
          · rw [dif_pos hclean] at hsuccess
            cases hsuccess
          · rw [dif_neg hclean] at hsuccess
            cases hsuccess
    | sealed ph =>
        have hAph : PhaseHolds A s.cfg ph := by
          simpa [hstage] using hstageSound
        by_cases hdel : EndpointDeleted A D
        · exact
            endpointDeleted_attack_tagged_of_same
              F A D hsame hdel
        · rw [dif_neg hdel, hstage] at hsuccess
          dsimp only at hsuccess
          by_cases hhit : cleanLiveHitService A ph e
          · exact
              boundary_clean_live_hit_deletes_j
                F A s.cfg hsame ph hAph hB hnot e hhit
          · rw [dif_neg hhit] at hsuccess
            cases hsuccess

theorem liveHitPrep_active_sound
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 D0 : Config n}
    (F : TripleFrame ring C0)
    (A : SectorFrame ring D0)
    (hsame : SameAttackGeometry F A)
    (hb : F.b = 1)
    (s s' : LiveHitPrepState n)
    (e : Fin n)
    (hsound : LiveHitSound F A s)
    (hactive :
      liveHitPrepStep ring A s e = .active s') :
    LiveHitSound F A s' := by
  classical
  have hcfg :=
    liveHitPrep_active_config ring A s s' e hactive
  unfold LiveHitSound at hsound
  rcases hsound with htag | hgood
  · refine .inl ?_
    rw [hcfg]
    exact taggedDeleted_step F s.cfg e htag
  · rcases hgood with ⟨hnot, hB, hstageSound⟩
    let D := stepE ring s.cfg e
    by_cases htagD : TaggedDeleted F D
    · refine .inl ?_
      rw [hcfg]
      exact htagD
    · have hBstep :=
        boundaryBPhase_step
          hSealed F hb s.cfg hB hnot e
      have hBD : BoundaryBPhase F D := by
        rcases hBstep with htag' | hphase'
        · exact False.elim (htagD htag')
        · exact hphase'
      cases hstage : s.stage with
      | pre =>
          have hApre :
              CRInteriorFollowers A s.cfg := by
            simpa [hstage] using hstageSound
          have hdelA : ¬ EndpointDeleted A D := by
            intro hdel
            exact htagD
              (endpointDeleted_attack_tagged_of_same
                F A D hsame hdel)
          have hintD :=
            crInteriorFollowers_step
              A s.cfg e hApre
          by_cases hclean : CleanReady A D
          · have hactive' := hactive
            unfold liveHitPrepStep at hactive'
            dsimp only at hactive'
            rw [dif_neg hdelA, hstage,
              dif_pos hclean] at hactive'
            cases hactive'
            unfold LiveHitSound
            refine .inr ⟨htagD, hBD, ?_⟩
            have hsector :
                SectorInteriorFollowers A D := by
              simpa [D, SectorInteriorFollowers,
                CRInteriorFollowers] using hintD
            exact ⟨hsector, hclean⟩
          · have hactive' := hactive
            unfold liveHitPrepStep at hactive'
            dsimp only at hactive'
            rw [dif_neg hdelA, hstage,
              dif_neg hclean] at hactive'
            cases hactive'
            unfold LiveHitSound
            refine .inr ⟨htagD, hBD, ?_⟩
            simpa [D] using hintD
      | sealed ph =>
          have hAph :
              PhaseHolds A s.cfg ph := by
            simpa [hstage] using hstageSound
          have hAalive :
              ¬ EndpointDeleted A s.cfg := by
            intro hdel
            exact hnot
              (endpointDeleted_attack_tagged_of_same
                F A s.cfg hsame hdel)
          have hdelA : ¬ EndpointDeleted A D := by
            intro hdel
            exact htagD
              (endpointDeleted_attack_tagged_of_same
                F A D hsame hdel)
          by_cases hhit : cleanLiveHitService A ph e
          · have hactive' := hactive
            unfold liveHitPrepStep at hactive'
            dsimp only at hactive'
            rw [dif_neg hdelA, hstage] at hactive'
            dsimp only at hactive'
            rw [dif_pos hhit] at hactive'
            cases hactive'
          · have hactive' := hactive
            unfold liveHitPrepStep at hactive'
            dsimp only at hactive'
            rw [dif_neg hdelA, hstage] at hactive'
            dsimp only at hactive'
            rw [dif_neg hhit] at hactive'
            cases hactive'
            have hphaseD :
                PhaseHolds A D
                  (nextSectorPhase A ph e) := by
              rcases
                  hSealed ring A s.cfg ph
                    hAph hAalive e with
                hdel | ⟨ph', hph', htr⟩
              · exact False.elim (hdelA hdel)
              · rw [htr] at hph'
                exact hph'
            unfold LiveHitSound
            exact .inr ⟨htagD, hBD, hphaseD⟩

/-- The File-3 live-hit monitor upper-bounds the actual tagged-deletion cost
once B is a one-edge Ready/Dummy target. -/
theorem liveHitPrepCost_dom_tagged_boundary
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (D : Config n)
    (A : SectorFrame ring D)
    (hsame : SameAttackGeometry F A)
    (hb : F.b = 1)
    (hB : BoundaryBPhase F D)
    (htag : ¬ TaggedDeleted F D) :
    ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) D T ≤
        liveHitPrepCostNumerator ring D A T := by
  intro T
  classical
  have hint0 : CRInteriorFollowers A D :=
    A.interior_follower
  have hsector0 : SectorInteriorFollowers A D := by
    simpa [SectorInteriorFollowers, CRInteriorFollowers]
      using hint0
  have hstartSound :
      LiveHitSound F A (liveHitPrepStart D A) := by
    by_cases hclean : CleanReady A D
    · unfold liveHitPrepStart
      try dsimp only
      rw [dif_pos hclean]
      exact
        .inr ⟨htag, hB, ⟨hsector0, hclean⟩⟩
    · unfold liveHitPrepStart
      try dsimp only
      rw [dif_neg hclean]
      exact
        .inr ⟨htag, hB, hint0⟩
  have key :
      ∀ T (s : LiveHitPrepState n),
        LiveHitSound F A s →
        costNumerator
            (stepE ring) (TaggedDeleted F) s.cfg T ≤
          truncatedActiveCostNumerator
            (liveHitPrepStep ring A) (.active s) T := by
    intro T
    induction T with
    | zero =>
        intro s hs
        simp [truncatedActiveCostNumerator]
    | succ T ih =>
        intro s hs
        by_cases hdone : TaggedDeleted F s.cfg
        · rw [costNumerator_terminal
            (stepE ring) (TaggedDeleted F)
            s.cfg hdone]
          exact Nat.zero_le _
        · rw [costNumerator_succ
            (stepE ring) (TaggedDeleted F)
            s.cfg hdone]
          simp only [truncatedActiveCostNumerator]
          apply Nat.add_le_add_left
          apply ofFn_sum_le
          intro e
          generalize hnode :
            liveHitPrepStep ring A s e = node
          cases node with
          | success =>
              have htagChild :=
                liveHitPrep_success_tagged
                  F A hsame hb s e hs hnode
              rw [costNumerator_terminal
                (stepE ring) (TaggedDeleted F)
                (stepE ring s.cfg e) htagChild]
              simp [truncatedActiveCostNumerator]
          | failure =>
              exact False.elim
                ((liveHitPrep_ne_failure ring A s e) hnode)
          | active s' =>
              have hcfg :=
                liveHitPrep_active_config
                  ring A s s' e hnode
              have hs' :=
                liveHitPrep_active_sound
                  hSealed F A hsame hb
                  s s' e hs hnode
              have hi := ih s' hs'
              simpa [hcfg] using hi
  have hkey :=
    key T (liveHitPrepStart D A) hstartSound
  have hcfg0 : (liveHitPrepStart D A).cfg = D := by
    unfold liveHitPrepStart
    split <;> rfl
  rw [hcfg0] at hkey
  simpa [liveHitPrepCostNumerator] using hkey
/-! ## Endpoint-retaining same-horizon composition -/
noncomputable def boundaryBindNumerator
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    Config n → Nat → Nat
  | _, 0 => 0
  | D, T + 1 => by
      classical
      exact
        if _h : CRDone F.B D then
          costNumerator
            (stepE ring) (TaggedDeleted F) D (T + 1)
        else
          (List.ofFn (fun e : Fin n =>
            boundaryBindNumerator
              ring F (stepE ring D e) T)).sum
/-! ## Boundary theorem -/
theorem boundary_ld_proved
    (hSealed : SealedStepSpec)
    (hLive : CleanLiveHitCost)
    {n : Nat} (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (_h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C)
    (hb : F.b = 1) :
    ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (6 * n * (F.a + 1)) := by
  classical
  intro T
  have hA0 : CRInteriorFollowers F.A C :=
    F.A.interior_follower
  have hB0 : CRInteriorFollowers F.B C :=
    F.B.interior_follower
  have hseq :
      ∀ t (D : Config n),
        PPL.Elim.PB ring D →
        CRInteriorFollowers F.A D →
        CRInteriorFollowers F.B D →
        costNumerator
            (stepE ring) (TaggedDeleted F) D t ≤
          costNumerator
              (stepE ring) (CRDone F.B) D t +
            boundaryBindNumerator ring F D t := by
    intro t
    induction t with
    | zero =>
        intro D hPBD hAD hBD
        simp [boundaryBindNumerator]
    | succ t ih =>
        intro D hPBD hAD hBD
        by_cases hready : CRDone F.B D
        · rw [costNumerator_terminal
            (stepE ring) (CRDone F.B)
            D hready]
          simp [boundaryBindNumerator, hready]
        · by_cases htag : TaggedDeleted F D
          · rw [costNumerator_terminal
              (stepE ring) (TaggedDeleted F)
              D htag]
            exact Nat.zero_le _
          · rw [
              costNumerator_succ
                (stepE ring) (TaggedDeleted F)
                D htag,
              costNumerator_succ
                (stepE ring) (CRDone F.B)
                D hready
            ]
            simp only [boundaryBindNumerator, dif_neg hready]
            have hchildren :
                (List.ofFn (fun e : Fin n =>
                  costNumerator
                    (stepE ring) (TaggedDeleted F)
                    (stepE ring D e) t)).sum ≤
                (List.ofFn (fun e : Fin n =>
                  costNumerator
                      (stepE ring) (CRDone F.B)
                      (stepE ring D e) t +
                    boundaryBindNumerator
                      ring F (stepE ring D e) t)).sum := by
              apply ofFn_sum_le
              intro e
              exact ih
                (stepE ring D e)
                (pbStepClosure ring D e hPBD)
                (crInteriorFollowers_step
                  F.A D e hAD)
                (crInteriorFollowers_step
                  F.B D e hBD)
            rw [ofFn_sum_add] at hchildren
            omega
  have hbind :
      ∀ t (D : Config n),
        PPL.Elim.PB ring D →
        CRInteriorFollowers F.A D →
        CRInteriorFollowers F.B D →
        boundaryBindNumerator ring F D t ≤
          n ^ t * (n * (6 * F.a - 1)) := by
    intro t
    induction t with
    | zero =>
        intro D hPBD hAD hBD
        simp [boundaryBindNumerator]
    | succ t ih =>
        intro D hPBD hAD hBD
        by_cases hready : CRDone F.B D
        · simp only [boundaryBindNumerator, dif_pos hready]
          by_cases htag : TaggedDeleted F D
          · rw [costNumerator_terminal
              (stepE ring) (TaggedDeleted F)
              D htag]
            exact Nat.zero_le _
          · have hclean : CleanReady F.B D := by
              rcases hready with hdel | hclean
              · exact False.elim
                  (htag
                    (endpointDeletedB_tagged_twoLeader
                      F hdel))
              · exact hclean
            have hBsector :
                SectorInteriorFollowers F.B D := by
              simpa [SectorInteriorFollowers,
                CRInteriorFollowers] using hBD
            have hBready :
                BoundaryBPhase F D :=
              .inl ⟨hBsector, hclean⟩
            let Acur :=
              boundaryAttackFrame F D htag hAD
            have hsame :
                SameAttackGeometry F Acur := by
              exact ⟨rfl, rfl, rfl⟩
            have hdom :=
              liveHitPrepCost_dom_tagged_boundary
                hSealed F D Acur hsame hb
                hBready htag (t + 1)
            unfold CleanLiveHitCost at hLive
            have hlive :=
              hLive ring D hPBD Acur (t + 1)
            calc
              costNumerator
                  (stepE ring) (TaggedDeleted F)
                  D (t + 1) ≤
                liveHitPrepCostNumerator
                  ring D Acur (t + 1) := hdom
              _ ≤ n ^ (t + 1) *
                    (n * (6 * Acur.gap - 1)) := hlive
              _ = n ^ (t + 1) *
                    (n * (6 * F.a - 1)) := by
                  simp [Acur, boundaryAttackFrame, F.A_gap]
        · simp only [boundaryBindNumerator, dif_neg hready]
          calc
            (List.ofFn (fun e : Fin n =>
              boundaryBindNumerator
                ring F (stepE ring D e) t)).sum ≤
                (List.ofFn (fun _ : Fin n =>
                  n ^ t *
                    (n * (6 * F.a - 1)))).sum := by
              apply ofFn_sum_le
              intro e
              exact ih
                (stepE ring D e)
                (pbStepClosure ring D e hPBD)
                (crInteriorFollowers_step
                  F.A D e hAD)
                (crInteriorFollowers_step
                  F.B D e hBD)
            _ = n *
                (n ^ t *
                  (n * (6 * F.a - 1))) :=
              ofFn_sum_const n _
            _ = n ^ (t + 1) *
                (n * (6 * F.a - 1)) := by
              rw [Nat.pow_succ]
              ac_rfl
  have hfirstRaw :=
    cleanReady_cost_proved
      ring C hPB F.B T
  have hBgap : F.B.gap = 1 :=
    F.B_gap.trans hb
  have hfirst :
      costNumerator
          (stepE ring) (CRDone F.B) C T ≤
        n ^ T * (3 * n) := by
    simpa [hBgap] using hfirstRaw
  have htail :=
    hbind T C hPB hA0 hB0
  have hcompose :=
    hseq T C hPB hA0 hB0
  have hsmall :
      3 + (6 * F.a - 1) ≤
        6 * (F.a + 1) := by
    omega
  have hbudget :
      3 * n + n * (6 * F.a - 1) ≤
        6 * n * (F.a + 1) := by
    calc
      3 * n + n * (6 * F.a - 1) =
          n * (3 + (6 * F.a - 1)) := by
        rw [Nat.mul_add]
        simp [Nat.mul_comm]
      _ ≤ n * (6 * (F.a + 1)) :=
        Nat.mul_le_mul_left n hsmall
      _ = 6 * n * (F.a + 1) := by
        ac_rfl
  calc
    costNumerator
        (stepE ring) (TaggedDeleted F) C T ≤
      costNumerator
          (stepE ring) (CRDone F.B) C T +
        boundaryBindNumerator ring F C T := hcompose
    _ ≤ n ^ T * (3 * n) +
          n ^ T * (n * (6 * F.a - 1)) :=
      Nat.add_le_add hfirst htail
    _ = n ^ T *
          (3 * n + n * (6 * F.a - 1)) := by
      rw [Nat.mul_add]
    _ ≤ n ^ T *
          (6 * n * (F.a + 1)) :=
      Nat.mul_le_mul_left (n ^ T) hbudget
end PPL.Convergence.LDLocal
#print axioms PPL.Convergence.LDLocal.fin3_cases_boundary
#print axioms PPL.Convergence.LDLocal.rightNeighbor_ne_self_boundary
#print axioms PPL.Convergence.LDLocal.stepE_responder_boundary
#print axioms PPL.Convergence.LDLocal.rowE_kills_vulnerable_boundary
#print axioms PPL.Convergence.LDLocal.endpointDeleted_attack_tagged_of_same
#print axioms PPL.Convergence.LDLocal.boundary_clean_live_hit_deletes_j
#print axioms PPL.Convergence.LDLocal.boundaryBPhase_step
#print axioms PPL.Convergence.LDLocal.liveHitPrep_active_config
#print axioms PPL.Convergence.LDLocal.liveHitPrep_ne_failure
#print axioms PPL.Convergence.LDLocal.liveHitPrep_success_tagged
#print axioms PPL.Convergence.LDLocal.liveHitPrep_active_sound
#print axioms PPL.Convergence.LDLocal.liveHitPrepCost_dom_tagged_boundary
#print axioms PPL.Convergence.LDLocal.boundary_ld_proved
