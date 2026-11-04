import Leader.PPL.Elim.BoundaryRegime
import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# LD(736): File-3 clean-live cost endpoint

The clean-live monitor has two parts.  Before CleanReady it is charged by the
proved File-2 cost.  After CleanReady its stage is a deterministic sealed phase
monitor.  Endpoint deletion can only stop that monitor earlier, so its cost is
dominated by a phase-only stopped tree.

The phase-only rank is chosen so that the two distinguished Ready letters,
the exterior incoming edge and the source outgoing edge, jointly pay one
Bellman interaction.  This is the finite double-exception recurrence from the
File-3 plan and gives the exact sealed budget n * (3*d - 1).
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

private theorem truncatedActiveCostNumerator_success_zero
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ T, truncatedActiveCostNumerator step .success T = 0 := by
  intro T
  cases T <;> rfl

private def cleanLivePhaseValid (d : Nat) :
    SectorPhase → Prop
  | .ready => True
  | .dummy p => p < d
  | .live p => p < d
  | .ret q => 0 < q ∧ q < d

private theorem cleanLivePhaseValid_next
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : cleanLivePhaseValid A.gap ph)
    (e : Fin n) :
    cleanLivePhaseValid A.gap
      (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin,
          cleanLivePhaseValid, A.gap_pos]
      · by_cases hout : e = A.left
        · subst e
          by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hin, hgap,
              cleanLivePhaseValid]
          · have hgt : 1 < A.gap := by
              have hp := A.gap_pos
              omega
            simp [nextSectorPhase, hin, hgap,
              cleanLivePhaseValid, hgt]
        · simp [nextSectorPhase, hin, hout,
            cleanLivePhaseValid]
  | dummy p =>
      have hp : p < A.gap := by
        simpa [cleanLivePhaseValid] using h
      by_cases hsrv :
          e = advance ring A.left p
      · by_cases hnext : p + 1 < A.gap
        · simp [nextSectorPhase, hsrv, hnext,
            cleanLivePhaseValid]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hsrv, hnext, hgap,
              cleanLivePhaseValid]
          · simp only [nextSectorPhase, if_pos hsrv,
              if_neg hnext, if_neg hgap,
              cleanLivePhaseValid]
            have hpos := A.gap_pos
            omega
      · simpa [nextSectorPhase, hsrv,
          cleanLivePhaseValid] using hp
  | live p =>
      have hp : p < A.gap := by
        simpa [cleanLivePhaseValid] using h
      by_cases hsrv :
          e = advance ring A.left p
      · by_cases hnext : p + 1 < A.gap
        · simp [nextSectorPhase, hsrv, hnext,
            cleanLivePhaseValid]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hsrv, hnext, hgap,
              cleanLivePhaseValid]
          · simp only [nextSectorPhase, if_pos hsrv,
              if_neg hnext, if_neg hgap,
              cleanLivePhaseValid]
            have hpos := A.gap_pos
            omega
      · simpa [nextSectorPhase, hsrv,
          cleanLivePhaseValid] using hp
  | ret q =>
      have hq : 0 < q ∧ q < A.gap := by
        simpa [cleanLivePhaseValid] using h
      by_cases hsrv :
          e = advance ring A.left (q - 1)
      · by_cases hq1 : q = 1
        · simp [nextSectorPhase, hsrv, hq1,
            cleanLivePhaseValid]
        · simp only [nextSectorPhase, if_pos hsrv,
            if_neg hq1, cleanLivePhaseValid]
          omega
      · simpa [nextSectorPhase, hsrv,
          cleanLivePhaseValid] using hq

private structure CleanLivePhaseState (d : Nat) where
  phase : SectorPhase
  valid : cleanLivePhaseValid d phase

private noncomputable def cleanLivePhaseStep
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    CleanLivePhaseState A.gap →
      Fin n → StopNode (CleanLivePhaseState A.gap) := by
  classical
  exact fun s e =>
    if cleanLiveHitService A s.phase e then
      .success
    else
      .active {
        phase := nextSectorPhase A s.phase e
        valid :=
          cleanLivePhaseValid_next
            A s.phase s.valid e
      }

private def cleanLivePhaseRank (d : Nat) :
    SectorPhase → Nat
  | .ready => 3 * d - 1
  | .dummy p =>
      (2 * d - p - 1) + (3 * d - 1)
  | .live p => d - p
  | .ret q => q + (3 * d - 1)

private def cleanLivePhasePotential
    (n d : Nat) :
    StopNode (CleanLivePhaseState d) → Nat
  | .active s => n * cleanLivePhaseRank d s.phase
  | .success => 0
  | .failure => 0

private theorem sealedIncoming_ne_source_cleanLive
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    sealedIncomingEdge A ≠ A.left := by
  intro h
  have hn : 1 < n := by
    have hp := A.gap_pos
    have hlt := A.gap_lt_n
    omega
  have hr := congrArg ring.rightNeighbor h
  unfold sealedIncomingEdge at hr
  rw [rightNeighbor_leftNeighbor_twoLeader
    ring A.left] at hr
  exact
    (rightNeighbor_ne_self_boundary
      ring hn A.left) hr.symm

private theorem cleanLiveReady_pair_rank
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    cleanLivePhaseRank A.gap (.dummy 0) +
        cleanLivePhaseRank A.gap (.live 1) + 1 ≤
      2 * cleanLivePhaseRank A.gap .ready := by
  simp only [cleanLivePhaseRank]
  have hp := A.gap_pos
  omega

private theorem cleanLiveDummy_service_drop
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0)
    (p : Nat) (hp : p < A.gap) :
    cleanLivePhaseRank A.gap
        (nextSectorPhase A (.dummy p)
          (advance ring A.left p)) + 1 ≤
      cleanLivePhaseRank A.gap (.dummy p) := by
  simp only [nextSectorPhase, if_pos rfl]
  simp only [↓reduceIte]
  by_cases hnext : p + 1 < A.gap
  · rw [if_pos hnext]
    simp only [cleanLivePhaseRank]
    omega
  · rw [if_neg hnext]
    by_cases hgap : A.gap = 1
    · rw [if_pos hgap]
      simp only [cleanLivePhaseRank]
      omega
    · rw [if_neg hgap]
      simp only [cleanLivePhaseRank]
      have hpos := A.gap_pos
      omega

private theorem cleanLiveLive_service_miss_drop
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0)
    (p : Nat) (hp : p < A.gap)
    (hmiss :
      ¬ cleanLiveHitService A (.live p)
        (advance ring A.left p)) :
    cleanLivePhaseRank A.gap
        (nextSectorPhase A (.live p)
          (advance ring A.left p)) + 1 ≤
      cleanLivePhaseRank A.gap (.live p) := by
  have hne : p + 1 ≠ A.gap := by
    intro hEq
    exact hmiss ⟨rfl, hEq⟩
  have hnext : p + 1 < A.gap := by
    omega
  simp [nextSectorPhase, hnext,
    cleanLivePhaseRank]
  omega

private theorem cleanLiveReturn_service_drop
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0)
    (q : Nat) (hq0 : 0 < q) :
    cleanLivePhaseRank A.gap
        (nextSectorPhase A (.ret q)
          (advance ring A.left (q - 1))) + 1 ≤
      cleanLivePhaseRank A.gap (.ret q) := by
  simp only [nextSectorPhase, if_pos rfl]
  simp only [↓reduceIte]
  by_cases hq1 : q = 1
  · rw [if_pos hq1]
    simp only [cleanLivePhaseRank]
    omega
  · rw [if_neg hq1]
    simp only [cleanLivePhaseRank]
    omega

private theorem one_exception_bellman
    {n r : Nat}
    (a : Fin n) (f : Fin n → Nat)
    (hr : 0 < r)
    (ha : f a ≤ n * (r - 1))
    (hother :
      ∀ e, e ≠ a → f e ≤ n * r) :
    n + (List.ofFn f).sum ≤
      n * (n * r) := by
  let c := n * r
  let g : Fin n → Nat :=
    fun e => if e = a then f e else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = a
    · simp [g, he]
    · simpa [g, he] using hother e he
  have hsum0 :
      (List.ofFn f).sum ≤
        (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hsumg :
      (List.ofFn g).sum =
        f a + (n - 1) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
          a g c (by
            intro e he
            simp [g, he])
    simpa [g] using h
  have hsum :
      (List.ofFn f).sum ≤
        f a + (n - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hsum' :
      (List.ofFn f).sum ≤
        n * (r - 1) + (n - 1) * c :=
    Nat.le_trans hsum
      (Nat.add_le_add_right ha _)
  have hc :
      c = n + n * (r - 1) := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show r ≠ 0 by omega)
    subst r
    dsimp [c]
    rw [Nat.mul_succ]
    exact Nat.add_comm _ _
  have hnpos : 0 < n := by
    have haLt := a.isLt
    omega
  have hm :
      n * c = c + (n - 1) * c := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show n ≠ 0 by omega)
    rw [hq]
    simp [Nat.succ_mul, Nat.add_comm]
  have hfinal :
      n + (List.ofFn f).sum ≤ n * c := by
    calc
      n + (List.ofFn f).sum
          ≤ n +
              (n * (r - 1) +
                (n - 1) * c) :=
        Nat.add_le_add_left hsum' n
      _ = (n + n * (r - 1)) +
            (n - 1) * c := by
        omega
      _ = c + (n - 1) * c := by
        rw [← hc]
      _ = n * c := hm.symm
  simpa [c] using hfinal

private theorem two_exception_bellman
    {n r ra rb : Nat}
    (a b : Fin n) (f : Fin n → Nat)
    (hab : a ≠ b)
    (hpair : ra + rb + 1 ≤ 2 * r)
    (ha : f a ≤ n * ra)
    (hb : f b ≤ n * rb)
    (hother :
      ∀ e, e ≠ a → e ≠ b →
        f e ≤ n * r) :
    n + (List.ofFn f).sum ≤
      n * (n * r) := by
  let c := n * r
  let g : Fin n → Nat :=
    fun e =>
      if e = a then f e
      else if e = b then f e
      else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases hea : e = a
    · simp [g, hea]
    · by_cases heb : e = b
      · simp [g, hea, heb]
      · simpa [g, hea, heb] using
          hother e hea heb
  have hsum0 :
      (List.ofFn f).sum ≤
        (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hba : b ≠ a := Ne.symm hab
  have hsumg :
      (List.ofFn g).sum =
        f a + f b + (n - 2) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
          a b g c hab (by
            intro e hea heb
            simp [g, hea, heb])
    simpa [g, hab, hba] using h
  have hsum :
      (List.ofFn f).sum ≤
        f a + f b + (n - 2) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have habound :
      f a + f b ≤
        n * ra + n * rb :=
    Nat.add_le_add ha hb
  have hsum' :
      (List.ofFn f).sum ≤
        n * ra + n * rb +
          (n - 2) * c :=
    Nat.le_trans hsum
      (Nat.add_le_add_right habound _)
  have hhead :
      n + n * ra + n * rb ≤ c + c := by
    have hscale :=
      Nat.mul_le_mul_left n hpair
    calc
      n + n * ra + n * rb =
          n * (ra + rb + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      _ ≤ n * (2 * r) := hscale
      _ = c + c := by
        dsimp [c]
        simp only [Nat.two_mul, Nat.mul_add]
  have hn2 : 2 ≤ n := by
    by_cases hn : 2 ≤ n
    · exact hn
    · have hav : a.val = 0 := by
        have haLt := a.isLt
        omega
      have hbv : b.val = 0 := by
        have hbLt := b.isLt
        omega
      apply False.elim
      apply hab
      apply Fin.ext
      omega
  have hmul :
      n * c =
        (c + c) + (n - 2) * c := by
    have hsplit :
        n = 2 + (n - 2) := by
      omega
    calc
      n * c =
          (2 + (n - 2)) * c := by
        rw [← hsplit]
      _ = 2 * c + (n - 2) * c := by
        rw [Nat.add_mul]
      _ = (c + c) + (n - 2) * c := by
        rw [Nat.two_mul]
  have hfinal :
      n + (List.ofFn f).sum ≤
        (c + c) + (n - 2) * c := by
    omega
  calc
    n + (List.ofFn f).sum
        ≤ (c + c) + (n - 2) * c := hfinal
    _ = n * c := hmul.symm
    _ = n * (n * r) := by
      rfl

private theorem cleanLivePhase_bellman
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0) :
    NatBellmanSuperSolution
      (cleanLivePhaseStep A) 1
      (cleanLivePhasePotential n A.gap) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨ph, hvalid⟩
  cases ph with
  | ready =>
      let f : Fin n → Nat :=
        fun e =>
          cleanLivePhasePotential n A.gap
            (cleanLivePhaseStep A
              ({
                phase := .ready
                valid := hvalid
              } : CleanLivePhaseState A.gap)
              e)
      have hne :
          sealedIncomingEdge A ≠ A.left :=
        sealedIncoming_ne_source_cleanLive A
      have hin :
          f (sealedIncomingEdge A) ≤
            n *
              cleanLivePhaseRank A.gap
                (.dummy 0) := by
        simp [f, cleanLivePhaseStep,
          cleanLiveHitService, nextSectorPhase,
          cleanLivePhasePotential, hne]
      have hout :
          f A.left ≤
            n *
              cleanLivePhaseRank A.gap
                (.live 1) := by
        have hleft :
            A.left ≠ sealedIncomingEdge A :=
          Ne.symm hne
        by_cases hgap : A.gap = 1
        · simp [f, cleanLivePhaseStep,
            cleanLiveHitService, nextSectorPhase,
            cleanLivePhasePotential,
            cleanLivePhaseRank, hleft, hgap]
        · simp [f, cleanLivePhaseStep,
            cleanLiveHitService, nextSectorPhase,
            cleanLivePhasePotential,
            hleft, hgap]
      have hother :
          ∀ e,
            e ≠ sealedIncomingEdge A →
            e ≠ A.left →
            f e ≤
              n *
                cleanLivePhaseRank
                  A.gap .ready := by
        intro e hin' hout'
        simp [f, cleanLivePhaseStep,
          cleanLiveHitService, nextSectorPhase,
          cleanLivePhasePotential,
          hin', hout']
      have hbell :=
        two_exception_bellman
          (r :=
            cleanLivePhaseRank
              A.gap .ready)
          (ra :=
            cleanLivePhaseRank
              A.gap (.dummy 0))
          (rb :=
            cleanLivePhaseRank
              A.gap (.live 1))
          (sealedIncomingEdge A) A.left f hne
          (cleanLiveReady_pair_rank A)
          hin hout hother
      simpa only [Nat.one_mul, f,
        cleanLivePhasePotential] using hbell
  | dummy p =>
      have hp : p < A.gap := by
        simpa [cleanLivePhaseValid] using hvalid
      let f : Fin n → Nat :=
        fun e =>
          cleanLivePhasePotential n A.gap
            (cleanLivePhaseStep A
              ({
                phase := .dummy p
                valid := hvalid
              } : CleanLivePhaseState A.gap)
              e)
      have hr :
          0 <
            cleanLivePhaseRank
              A.gap (.dummy p) := by
        simp only [cleanLivePhaseRank]
        have hpos := A.gap_pos
        omega
      have hmiss :
          ¬ cleanLiveHitService A (.dummy p)
            (advance ring A.left p) := by
        simp [cleanLiveHitService]
      have hdrop :=
        cleanLiveDummy_service_drop
          A p hp
      have hle :
          cleanLivePhaseRank A.gap
              (nextSectorPhase A (.dummy p)
                (advance ring A.left p)) ≤
            cleanLivePhaseRank A.gap
              (.dummy p) - 1 := by
        omega
      have hreq :
          f (advance ring A.left p) ≤
            n *
              (cleanLivePhaseRank A.gap
                (.dummy p) - 1) := by
        simp only [f, cleanLivePhaseStep]
        rw [if_neg hmiss]
        simp only [cleanLivePhasePotential]
        exact Nat.mul_le_mul_left n hle
      have hother :
          ∀ e,
            e ≠ advance ring A.left p →
            f e ≤
              n *
                cleanLivePhaseRank
                  A.gap (.dummy p) := by
        intro e he
        have hmiss' :
            ¬ cleanLiveHitService A
              (.dummy p) e := by
          simp [cleanLiveHitService]
        simp only [f, cleanLivePhaseStep]
        rw [if_neg hmiss']
        simp [cleanLivePhasePotential,
          nextSectorPhase, he]
      have hbell :=
        one_exception_bellman
          (r :=
            cleanLivePhaseRank
              A.gap (.dummy p))
          (advance ring A.left p)
          f hr hreq hother
      simpa only [Nat.one_mul, f,
        cleanLivePhasePotential] using hbell
  | live p =>
      have hp : p < A.gap := by
        simpa [cleanLivePhaseValid] using hvalid
      let f : Fin n → Nat :=
        fun e =>
          cleanLivePhasePotential n A.gap
            (cleanLivePhaseStep A
              ({
                phase := .live p
                valid := hvalid
              } : CleanLivePhaseState A.gap)
              e)
      have hr :
          0 <
            cleanLivePhaseRank
              A.gap (.live p) := by
        simp only [cleanLivePhaseRank]
        omega
      have hreq :
          f (advance ring A.left p) ≤
            n *
              (cleanLivePhaseRank A.gap
                (.live p) - 1) := by
        by_cases hhit :
            cleanLiveHitService A (.live p)
              (advance ring A.left p)
        · simp only [f, cleanLivePhaseStep]
          rw [if_pos hhit]
          simp [cleanLivePhasePotential]
        · have hdrop :=
            cleanLiveLive_service_miss_drop
              A p hp hhit
          have hle :
              cleanLivePhaseRank A.gap
                  (nextSectorPhase A (.live p)
                    (advance ring A.left p)) ≤
                cleanLivePhaseRank A.gap
                  (.live p) - 1 := by
            omega
          simp only [f, cleanLivePhaseStep]
          rw [if_neg hhit]
          simp only [cleanLivePhasePotential]
          exact Nat.mul_le_mul_left n hle
      have hother :
          ∀ e,
            e ≠ advance ring A.left p →
            f e ≤
              n *
                cleanLivePhaseRank
                  A.gap (.live p) := by
        intro e he
        have hmiss :
            ¬ cleanLiveHitService A
              (.live p) e := by
          intro hhit
          exact he hhit.1
        simp only [f, cleanLivePhaseStep]
        rw [if_neg hmiss]
        simp [cleanLivePhasePotential,
          nextSectorPhase, he]
      have hbell :=
        one_exception_bellman
          (r :=
            cleanLivePhaseRank
              A.gap (.live p))
          (advance ring A.left p)
          f hr hreq hother
      simpa only [Nat.one_mul, f,
        cleanLivePhasePotential] using hbell
  | ret q =>
      have hq :
          0 < q ∧ q < A.gap := by
        simpa [cleanLivePhaseValid] using hvalid
      let f : Fin n → Nat :=
        fun e =>
          cleanLivePhasePotential n A.gap
            (cleanLivePhaseStep A
              ({
                phase := .ret q
                valid := hvalid
              } : CleanLivePhaseState A.gap)
              e)
      have hr :
          0 <
            cleanLivePhaseRank
              A.gap (.ret q) := by
        simp only [cleanLivePhaseRank]
        omega
      have hmiss :
          ¬ cleanLiveHitService A (.ret q)
            (advance ring A.left (q - 1)) := by
        simp [cleanLiveHitService]
      have hdrop :=
        cleanLiveReturn_service_drop
          A q hq.1
      have hle :
          cleanLivePhaseRank A.gap
              (nextSectorPhase A (.ret q)
                (advance ring A.left (q - 1))) ≤
            cleanLivePhaseRank A.gap
              (.ret q) - 1 := by
        omega
      have hreq :
          f (advance ring A.left (q - 1)) ≤
            n *
              (cleanLivePhaseRank A.gap
                (.ret q) - 1) := by
        simp only [f, cleanLivePhaseStep]
        rw [if_neg hmiss]
        simp only [cleanLivePhasePotential]
        exact Nat.mul_le_mul_left n hle
      have hother :
          ∀ e,
            e ≠ advance ring A.left (q - 1) →
            f e ≤
              n *
                cleanLivePhaseRank
                  A.gap (.ret q) := by
        intro e he
        have hmiss' :
            ¬ cleanLiveHitService A
              (.ret q) e := by
          simp [cleanLiveHitService]
        simp only [f, cleanLivePhaseStep]
        rw [if_neg hmiss']
        simp [cleanLivePhasePotential,
          nextSectorPhase, he]
      have hbell :=
        one_exception_bellman
          (r :=
            cleanLivePhaseRank
              A.gap (.ret q))
          (advance ring A.left (q - 1))
          f hr hreq hother
      simpa only [Nat.one_mul, f,
        cleanLivePhasePotential] using hbell

private theorem liveHitPrep_sealed_cost_le_phase
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0) :
    ∀ T (D : Config n) (ph : SectorPhase)
      (hvalid : cleanLivePhaseValid A.gap ph),
      truncatedActiveCostNumerator
          (liveHitPrepStep ring A)
          (.active {
            cfg := D
            stage := .sealed ph
          }) T ≤
        truncatedActiveCostNumerator
          (cleanLivePhaseStep A)
          (.active {
            phase := ph
            valid := hvalid
          }) T := by
  intro T
  induction T with
  | zero =>
      intro D ph hvalid
      simp [truncatedActiveCostNumerator]
  | succ T ih =>
      intro D ph hvalid
      simp only [truncatedActiveCostNumerator]
      apply Nat.add_le_add_left
      apply ofFn_sum_le
      intro e
      by_cases hdel :
          EndpointDeleted A
            (stepE ring D e)
      · have hphys :
            liveHitPrepStep ring A
              {
                cfg := D
                stage := .sealed ph
              } e = .success := by
          unfold liveHitPrepStep
          dsimp only
          rw [dif_pos hdel]
        rw [hphys,
          truncatedActiveCostNumerator_success_zero]
        exact Nat.zero_le _
      · by_cases hhit :
          cleanLiveHitService A ph e
        · have hphys :
              liveHitPrepStep ring A
                {
                  cfg := D
                  stage := .sealed ph
                } e = .success := by
            unfold liveHitPrepStep
            dsimp only
            rw [dif_neg hdel]
            rw [dif_pos hhit]
          have habs :
              cleanLivePhaseStep A
                {
                  phase := ph
                  valid := hvalid
                } e = .success := by
            simp [cleanLivePhaseStep, hhit]
          rw [hphys, habs]
          simp only [truncatedActiveCostNumerator_success_zero]
          exact Nat.le_refl 0
        · have hphys :
              liveHitPrepStep ring A
                {
                  cfg := D
                  stage := .sealed ph
                } e =
                .active {
                  cfg := stepE ring D e
                  stage :=
                    .sealed
                      (nextSectorPhase A ph e)
                } := by
            unfold liveHitPrepStep
            dsimp only
            rw [dif_neg hdel]
            rw [dif_neg hhit]
          have habs :
              cleanLivePhaseStep A
                {
                  phase := ph
                  valid := hvalid
                } e =
                .active {
                  phase :=
                    nextSectorPhase A ph e
                  valid :=
                    cleanLivePhaseValid_next
                      A ph hvalid e
                } := by
            simp [cleanLivePhaseStep, hhit]
          rw [hphys, habs]
          exact
            ih (stepE ring D e)
              (nextSectorPhase A ph e)
              (cleanLivePhaseValid_next
                A ph hvalid e)

private theorem liveHitPrep_sealed_ready_cost
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) :
    ∀ T,
      truncatedActiveCostNumerator
          (liveHitPrepStep ring A)
          (.active {
            cfg := D
            stage := .sealed .ready
          }) T ≤
        n ^ T *
          (n * (3 * A.gap - 1)) := by
  intro T
  let start : CleanLivePhaseState A.gap := {
    phase := .ready
    valid := True.intro
  }
  have hdom0 :=
    liveHitPrep_sealed_cost_le_phase
      ring A T D start.phase start.valid
  have hdom :
      truncatedActiveCostNumerator
          (liveHitPrepStep ring A)
          (.active {
            cfg := D
            stage := .sealed .ready
          }) T ≤
        truncatedActiveCostNumerator
          (cleanLivePhaseStep A)
          (.active start) T := by
    simpa [start] using hdom0
  have hbell :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (cleanLivePhaseStep A) 1
      (cleanLivePhasePotential n A.gap)
      (cleanLivePhase_bellman A)
      (.active start) T
  have htree :
      truncatedActiveCostNumerator
          (cleanLivePhaseStep A)
          (.active start) T ≤
        n ^ T *
          (n * (3 * A.gap - 1)) := by
    simpa [start, cleanLivePhasePotential,
      cleanLivePhaseRank] using hbell
  exact Nat.le_trans hdom htree

private theorem liveHitPrep_pre_cost
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0) :
    ∀ T (D : Config n),
      ¬ CRDone A D →
      truncatedActiveCostNumerator
          (liveHitPrepStep ring A)
          (.active {
            cfg := D
            stage := .pre
          }) T ≤
        costNumerator
            (stepE ring) (CRDone A) D T +
          n ^ T *
            (n * (3 * A.gap - 1)) := by
  intro T
  induction T with
  | zero =>
      intro D hnot
      simp [truncatedActiveCostNumerator]
  | succ T ih =>
      intro D hnot
      have hchildren :
          (List.ofFn (fun e : Fin n =>
            truncatedActiveCostNumerator
              (liveHitPrepStep ring A)
              (liveHitPrepStep ring A
                {
                  cfg := D
                  stage := .pre
                } e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            costNumerator
                (stepE ring) (CRDone A)
                (stepE ring D e) T +
              n ^ T *
                (n * (3 * A.gap - 1)))).sum := by
        apply ofFn_sum_le
        intro e
        by_cases hdel :
            EndpointDeleted A
              (stepE ring D e)
        · have hphys :
              liveHitPrepStep ring A
                {
                  cfg := D
                  stage := .pre
                } e = .success := by
            unfold liveHitPrepStep
            dsimp only
            rw [dif_pos hdel]
          have hdone :
              CRDone A
                (stepE ring D e) :=
            .inl hdel
          rw [hphys,
            truncatedActiveCostNumerator_success_zero,
            costNumerator_terminal
              (stepE ring) (CRDone A)
              (stepE ring D e) hdone]
          exact Nat.zero_le _
        · by_cases hclean :
            CleanReady A
              (stepE ring D e)
          · have hphys :
                liveHitPrepStep ring A
                  {
                    cfg := D
                    stage := .pre
                  } e =
                  .active {
                    cfg := stepE ring D e
                    stage := .sealed .ready
                  } := by
              unfold liveHitPrepStep
              dsimp only
              rw [dif_neg hdel]
              rw [dif_pos hclean]
            have hdone :
                CRDone A
                  (stepE ring D e) :=
              .inr hclean
            rw [hphys,
              costNumerator_terminal
                (stepE ring) (CRDone A)
                (stepE ring D e) hdone,
              Nat.zero_add]
            exact
              liveHitPrep_sealed_ready_cost
                ring A (stepE ring D e) T
          · have hnotChild :
                ¬ CRDone A
                  (stepE ring D e) := by
              intro hdone
              rcases hdone with hdel' | hclean'
              · exact hdel hdel'
              · exact hclean hclean'
            have hphys :
                liveHitPrepStep ring A
                  {
                    cfg := D
                    stage := .pre
                  } e =
                  .active {
                    cfg := stepE ring D e
                    stage := .pre
                  } := by
              unfold liveHitPrepStep
              dsimp only
              rw [dif_neg hdel]
              rw [dif_neg hclean]
            rw [hphys]
            exact ih (stepE ring D e) hnotChild
      rw [ofFn_sum_add, ofFn_sum_const] at hchildren
      have hpad :
          n *
              (n ^ T *
                (n * (3 * A.gap - 1))) =
            n ^ (T + 1) *
              (n * (3 * A.gap - 1)) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hpad] at hchildren
      rw [costNumerator_succ
        (stepE ring) (CRDone A)
        D hnot T]
      simp only [truncatedActiveCostNumerator]
      omega

private theorem sectorFrame_initial_not_deleted
    {n : Nat} {ring : DirectedRing n}
    {C : Config n}
    (A : SectorFrame ring C) :
    ¬ EndpointDeleted A C := by
  intro h
  rcases h with hleft | hright
  · have ht := A.left_leader
    rw [hleft] at ht
    cases ht
  · have ht := A.right_leader
    rw [hright] at ht
    cases ht

theorem cleanLiveHitCost
    (_hSealed : SealedStepSpec) :
    CleanLiveHitCost := by
  classical
  intro n ring C hPB A T
  have halive :
      ¬ EndpointDeleted A C :=
    sectorFrame_initial_not_deleted A
  by_cases hclean : CleanReady A C
  · have hstart :
        liveHitPrepStart C A = {
          cfg := C
          stage := .sealed .ready
        } := by
      unfold liveHitPrepStart
      rw [dif_pos hclean]
    have hsealed :=
      liveHitPrep_sealed_ready_cost
        ring A C T
    have hcoef :
        n * (3 * A.gap - 1) ≤
          n * (6 * A.gap - 1) := by
      apply Nat.mul_le_mul_left
      have hp := A.gap_pos
      omega
    unfold liveHitPrepCostNumerator
    rw [hstart]
    exact Nat.le_trans hsealed
      (Nat.mul_le_mul_left (n ^ T) hcoef)
  · have hnot :
        ¬ CRDone A C := by
      intro hdone
      rcases hdone with hdel | hready
      · exact halive hdel
      · exact hclean hready
    have hstart :
        liveHitPrepStart C A = {
          cfg := C
          stage := .pre
        } := by
      unfold liveHitPrepStart
      rw [dif_neg hclean]
    have hpre :=
      liveHitPrep_pre_cost
        ring A T C hnot
    have hcr :=
      cleanReady_cost_proved
        ring C hPB A T
    have hcoef :
        3 * n * A.gap +
            n * (3 * A.gap - 1) =
          n * (6 * A.gap - 1) := by
      have hfirst :
          3 * n * A.gap =
            n * (3 * A.gap) := by
        ac_rfl
      rw [hfirst]
      rw [← Nat.mul_add]
      congr 1
      have hp := A.gap_pos
      omega
    unfold liveHitPrepCostNumerator
    rw [hstart]
    calc
      truncatedActiveCostNumerator
          (liveHitPrepStep ring A)
          (.active {
            cfg := C
            stage := .pre
          }) T
          ≤ costNumerator
                (stepE ring) (CRDone A) C T +
              n ^ T *
                (n * (3 * A.gap - 1)) := hpre
      _ ≤ n ^ T * (3 * n * A.gap) +
            n ^ T *
              (n * (3 * A.gap - 1)) :=
        Nat.add_le_add_right hcr _
      _ = n ^ T *
            (3 * n * A.gap +
              n * (3 * A.gap - 1)) := by
        rw [Nat.mul_add]
      _ = n ^ T *
            (n * (6 * A.gap - 1)) := by
        rw [hcoef]

theorem boundary_ld_sealed
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (h2 : 2 ≤ PPL.Elim.leaderCount C)
    (F : TripleFrame ring C)
    (hb : F.b = 1) :
    ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (6 * n * (F.a + 1)) := by
  exact
    boundary_ld_proved
      hSealed (cleanLiveHitCost hSealed)
      ring C hPB h2 F hb

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.cleanLiveHitCost
#print axioms PPL.Convergence.LDLocal.boundary_ld_sealed


