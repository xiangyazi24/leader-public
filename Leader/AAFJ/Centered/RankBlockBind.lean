import Leader.AAFJ.Centered.RankBlockRace
import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# Physical zero-time bind for the centered rank block

This module composes the payload-retaining fire stage with the tracked-bullet
race.  A fire terminal switches to the race without consuming an edge.  If
either stage lowers rank, all remaining scheduler coordinates are absorbed
only after that actual smaller-rank endpoint has been reached.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RankBlockBind

open BarrierAlgebra
open SingleBarrierSanitation
open RenewalSearch
open NoDropLaterShield
open RankBlockTrial
open RankBlockRace
open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLResearchFormulation

set_option autoImplicit false

/-! ## Precisely typed fire terminals -/

inductive FireSuccess {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) : Type where
  | fired (X : Fin n -> State k) (race : FiredRaceState hk ring X)
      (rank_eq : Phi X = r)
  | dropped (X : Fin n -> State k) (rank_lt : Phi X < r)

structure FireFailure {n k : Nat} (ring : DirectedRing n) where
  config : Fin n -> State k

noncomputable def firePayloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (e : Fin n) :
    PayloadNode (FireProofState hk ring r)
      (FireSuccess (r := r) hk ring) (FireFailure (k := k) ring) :=
  match s.next hn3 hndvd e with
  | a@(.active _ _ _) => .active a
  | .fired X F hr => .success (.fired X F hr)
  | .dropped X h => .success (.dropped X h)
  | .missed X => .failure ⟨X⟩

@[simp] theorem eraseStep_firePayloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    (eraseStep (firePayloadStep (hk := hk) (ring := ring) (r := r)
      hn3 hndvd) : FireProofState hk ring r -> Fin n ->
        StopNode (FireProofState hk ring r)) =
      (FireProofState.stoppedStep (hk := hk) (ring := ring) (r := r)
        hn3 hndvd : FireProofState hk ring r -> Fin n ->
          StopNode (FireProofState hk ring r)) := by
  funext s e
  unfold eraseStep firePayloadStep FireProofState.stoppedStep
  cases h : s.next hn3 hndvd e <;> rfl

/-- The typed fire tree has exactly the already-proved payload fire mass. -/
theorem typedFire_success_quarter_by_two_mul
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    n ^ (2 * n) <= 4 *
      successMass (firePayloadStep (r := r) hn3 hndvd)
        (.active (.active X F hrank)) (2 * n) := by
  have h := freshFire_success_quarter_by_two_mul
    hn3 hndvd X F hrank
  rw [successMass_eq_successCount,
    FireProofState.eraseStep_payloadStep] at h
  rw [successMass_eq_successCount, eraseStep_firePayloadStep]
  exact h

/-! ## Renewal terminals with their reachable rank semantics -/

/-- Reachable active renewal state at the fixed plateau rank `r`.  The
equality is carried outside `RenewalProofState` because its `good`
constructor intentionally stores only the physical freshness certificate. -/
structure RenewalActive {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) where
  state : RenewalProofState (r := r) hk ring
  active : ¬ state.IsTerminal
  rank_eq : PhiAt ring state.tail state.config = r

/-- Canonical wrapper for the first active-leg constructor. -/
def RenewalActive.ofFirst {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (state : AheadState (r := r) hk ring C tail) :
    RenewalActive (r := r) hk ring where
  state := .first state
  active := by simp [RenewalProofState.IsTerminal]
  rank_eq := state.rank_eq

/-- Canonical wrapper for the second active-leg constructor. -/
def RenewalActive.ofSecond {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (firstUsed : Nat) (hfirst : firstUsed <= n)
    (state : SweptCover (r := r) hk ring C tail)
    (hspan : state.frame.targetSteps <= n / 2) :
    RenewalActive (r := r) hk ring where
  state := .second firstUsed hfirst state hspan
  active := by simp [RenewalProofState.IsTerminal]
  rank_eq := state.rank_eq

/-- Literal first renewal endpoint.  Every inhabitant is semantically usable:
a drop is already final, while a good endpoint contains both the exact
`GoodFreshRenewal` payload and the plateau equality needed to start fire. -/
inductive RenewalSuccess {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) : Type where
  | dropped (state : RenewalProofState (r := r) hk ring)
      (rank_lt : PhiAt ring state.tail state.config < r)
  | good (state : RenewalProofState (r := r) hk ring)
      (certificate : Nonempty
        (GoodFreshRenewal hk ring state.config state.tail))
      (rank_eq : PhiAt ring state.tail state.config = r)

/-- Initial proof-indexed renewal state at the literal input cut. -/
noncomputable def initialRenewalActive {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) : RenewalActive (r := r) hk ring where
  state := initialRenewalProofState hk ring C tail hone hrank hr1
  active := by
    change ¬ (initialRenewalProofState hk ring C tail hone hrank hr1).IsTerminal
    simp [initialRenewalProofState, RenewalProofState.IsTerminal]
  rank_eq := by
    change PhiAt ring
      (initialRenewalProofState hk ring C tail hone hrank hr1).tail
      (initialRenewalProofState hk ring C tail hone hrank hr1).config = r
    simpa [initialRenewalProofState, RenewalProofState.tail,
      RenewalProofState.config] using hrank

/-- A strict drop below the fixed rank cannot inhabit either active renewal
constructor. -/
theorem RenewalProofState.terminal_of_rank_lt {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring)
    (rank_lt : PhiAt ring state.tail state.config < r) :
    state.IsTerminal := by
  cases state with
  | first active =>
      exfalso
      have hrank := active.rank_eq
      simp [RenewalProofState.tail, RenewalProofState.config] at rank_lt
      omega
  | second firstUsed hfirst active hspan =>
      exfalso
      have hrank := active.rank_eq
      simp [RenewalProofState.tail, RenewalProofState.config] at rank_lt
      omega
  | good used certificate => simp [RenewalProofState.IsTerminal]
  | dropped used drop => simp [RenewalProofState.IsTerminal]

/-- One literal active renewal interaction has rank at most the fixed plateau
rank.  This transports the one-barrier physical monotonicity theorem through
the exact configuration and moving-tail projections of `renewalProofNext`. -/
theorem RenewalActive.next_rank_le {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : RenewalActive (r := r) hk ring) (selected : Fin n) :
    let next := renewalProofNext hk ring hn3 hndvd s.state selected
    PhiAt ring next.tail next.config <= r := by
  let next := renewalProofNext hk ring hn3 hndvd s.state selected
  have hmono := Rank.oneBarrier_phi_step_le hk ring hn3 s.state.config
    s.state.tail selected hndvd (s.state.active_oneBarrier s.active)
  have hconfig := renewalProofNext_configuration hk ring hn3 hndvd s.state
    selected s.active
  have htail := renewalProofNext_tail hk ring hn3 hndvd s.state selected
    s.active
  change PhiAt ring next.tail next.config <= r
  rw [hconfig, htail]
  calc
    PhiAt ring (postStepBarrier hk ring s.state.config s.state.tail selected)
        (OneBarrierCleanup.step hk ring s.state.config selected) <=
        PhiAt ring s.state.tail s.state.config := by
      simpa [postStepBarrier, OneBarrierCleanup.step] using hmono.2
    _ = r := s.rank_eq

/-- The literal successor paired with the plateau upper bound proved from its
reachable active parent.  Packaging the dependent proof with the value keeps
the subsequent constructor classification proof-relevant and reducible. -/
structure RenewalChild {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) where
  state : RenewalProofState (r := r) hk ring
  rank_le : PhiAt ring state.tail state.config <= r

noncomputable def RenewalActive.child {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : RenewalActive (r := r) hk ring) (selected : Fin n) :
    RenewalChild (r := r) hk ring where
  state := renewalProofNext hk ring hn3 hndvd s.state selected
  rank_le := s.next_rank_le hn3 hndvd selected

/-- Classify the exact reachable child.  Active constructors already carry
rank equality.  A bare `good` constructor does not, so only that case uses the
proof-indexed upper bound; if it is already smaller, it stops as a drop. -/
def RenewalChild.payloadNode {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RenewalChild (r := r) hk ring ->
    PayloadNode (RenewalActive (r := r) hk ring)
      (RenewalSuccess (r := r) hk ring) (RenewalActive (r := r) hk ring)
  | ⟨.first active, _⟩ => .active (RenewalActive.ofFirst active)
  | ⟨.second firstUsed hfirst active hspan, _⟩ =>
      .active (RenewalActive.ofSecond firstUsed hfirst active hspan)
  | ⟨.good (C := C) (tail := tail) used certificate, hle⟩ =>
      if hdrop : PhiAt ring tail C < r then
        .success (.dropped (.good used certificate) hdrop)
      else
        .success (.good (.good used certificate) certificate
          (Nat.le_antisymm hle (Nat.le_of_not_gt hdrop)))
  | ⟨.dropped used drop, _⟩ =>
      .success (.dropped (.dropped used drop) drop)

/-- Endpoint-preserving renewal transition. -/
noncomputable def renewalPayloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : RenewalActive (r := r) hk ring) (selected : Fin n) :
    PayloadNode (RenewalActive (r := r) hk ring)
      (RenewalSuccess (r := r) hk ring) (RenewalActive (r := r) hk ring) :=
  (s.child hn3 hndvd selected).payloadNode

/-- The proof-indexed tree has exactly the original renewal success mass.
The equality is child-for-child; only the terminal payload type is refined. -/
theorem renewalSearch_successMass_eq_typed
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : RenewalActive (r := r) hk ring) : forall T,
    successMass (renewalSearchStep hk ring hn3 hndvd)
        (.active s.state) T =
      successMass (renewalPayloadStep (r := r) hn3 hndvd)
        (.active s) T := by
  intro T
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      simp only [successMass, PayloadFiniteStoppingTree.stepNode]
      apply ofFn_sum_eq
      intro selected
      generalize hchild : s.child hn3 hndvd selected = child
      cases child with
      | mk next hle =>
        have hnextRaw : renewalProofNext hk ring hn3 hndvd s.state selected =
            next := by
          have h := congrArg RenewalChild.state hchild
          simpa [RenewalActive.child] using h
        cases next with
        | first active =>
            let s' : RenewalActive (r := r) hk ring :=
              RenewalActive.ofFirst active
            have hsearch : renewalSearchStep hk ring hn3 hndvd s.state
                selected = .active (.first active) := by
              simp [renewalSearchStep, hnextRaw,
                RenewalProofState.IsTerminal]
            have htyped : renewalPayloadStep (r := r) hn3 hndvd s selected =
                .active s' := by
              simp [renewalPayloadStep, hchild, RenewalChild.payloadNode, s']
            rw [hsearch, htyped]
            exact ih s'
        | second firstUsed hfirst active hspan =>
            let s' : RenewalActive (r := r) hk ring :=
              RenewalActive.ofSecond firstUsed hfirst active hspan
            have hsearch : renewalSearchStep hk ring hn3 hndvd s.state
                selected = .active (.second firstUsed hfirst active hspan) := by
              simp [renewalSearchStep, hnextRaw,
                RenewalProofState.IsTerminal]
            have htyped : renewalPayloadStep (r := r) hn3 hndvd s selected =
                .active s' := by
              simp [renewalPayloadStep, hchild, RenewalChild.payloadNode, s']
            rw [hsearch, htyped]
            exact ih s'
        | @good C tail used certificate =>
            have hsearch : renewalSearchStep hk ring hn3 hndvd s.state
                selected = .success (.good used certificate) := by
              simp [renewalSearchStep, hnextRaw,
                RenewalProofState.IsTerminal]
            rw [hsearch]
            by_cases hdrop : PhiAt ring tail C < r
            · have htyped : renewalPayloadStep (r := r) hn3 hndvd s
                  selected = .success (.dropped (.good used certificate)
                    hdrop) := by
                simp [renewalPayloadStep, hchild, RenewalChild.payloadNode,
                  hdrop]
              rw [htyped, successMass_success, successMass_success]
            · have heq : PhiAt ring tail C = r :=
                Nat.le_antisymm hle (Nat.le_of_not_gt hdrop)
              have htyped : renewalPayloadStep (r := r) hn3 hndvd s
                  selected = .success (.good (.good used certificate)
                    certificate heq) := by
                simp [renewalPayloadStep, hchild, RenewalChild.payloadNode,
                  hdrop]
              rw [htyped, successMass_success, successMass_success]
        | @dropped C tail used drop =>
            have hsearch : renewalSearchStep hk ring hn3 hndvd s.state
                selected = .success (.dropped used drop) := by
              simp [renewalSearchStep, hnextRaw,
                RenewalProofState.IsTerminal]
            have htyped : renewalPayloadStep (r := r) hn3 hndvd s selected =
                .success (.dropped (.dropped used drop) drop) := by
              simp [renewalPayloadStep, hchild, RenewalChild.payloadNode]
            rw [hsearch, htyped, successMass_success, successMass_success]

theorem renewalSearch_successMass_le_typed
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : RenewalActive (r := r) hk ring) (T : Nat) :
    successMass (renewalSearchStep hk ring hn3 hndvd)
        (.active s.state) T <=
      successMass (renewalPayloadStep (r := r) hn3 hndvd)
        (.active s) T := by
  exact Nat.le_of_eq (renewalSearch_successMass_eq_typed hn3 hndvd s T)

/-- Half-mass renewal theorem with a success type that is strong enough for
physical endpoint-dependent continuation. -/
theorem initialTypedRenewal_success_half_by_eight_mul_sq
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (8 * n ^ 2) <= 2 *
      successMass (renewalPayloadStep (r := r) hn3 hndvd)
        (.active (initialRenewalActive hk ring C tail hone hrank hr1))
        (8 * n ^ 2) := by
  have hbase := initialRenewalSearch_success_half_by_eight_mul_sq
    hk ring hn3 hndvd C tail hone hrank hr1
  have hdom := renewalSearch_successMass_le_typed hn3 hndvd
    (initialRenewalActive hk ring C tail hone hrank hr1) (8 * n ^ 2)
  exact Nat.le_trans hbase (Nat.mul_le_mul_left 2 hdom)

/-! ## Scheduler-coordinate reindexing -/

/-- Reinterpret each raw scheduler symbol through a state-dependent edge
bijection.  This changes labels, never the chronological position of a
transition. -/
def edgeReindexedPayloadStep {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (edgeView : A -> Fin n -> Fin n) : A -> Fin n -> PayloadNode A S F :=
  fun state rawEdge => step state (edgeView state rawEdge)

private theorem bindListSum_eq_of_perm {xs ys : List Nat}
    (hperm : xs.Perm ys) : xs.sum = ys.sum := by
  induction hperm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Nat.add_left_comm ..
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem bindNodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n -> A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- A finite uniform sum is invariant under an explicitly inverted edge
view. -/
private theorem bindFinSum_reindex {n : Nat}
    (p q : Fin n -> Fin n)
    (hleft : forall x, q (p x) = x)
    (hright : forall x, p (q x) = x)
    (f : Fin n -> Nat) :
    (List.ofFn (fun x => f (p x))).sum = (List.ofFn f).sum := by
  have hpInjective : Function.Injective p := by
    intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  have hpNodup : (List.ofFn p).Nodup :=
    bindNodup_ofFn_of_injective p hpInjective
  have hidNodup : (List.ofFn (fun x : Fin n => x)).Nodup :=
    bindNodup_ofFn_of_injective (fun x : Fin n => x) (fun _ _ h => h)
  have hperm : (List.ofFn p).Perm
      (List.ofFn (fun x : Fin n => x)) := by
    apply (List.perm_ext_iff_of_nodup hpNodup hidNodup).2
    intro x
    constructor
    · intro _
      exact List.mem_ofFn.mpr ⟨x, rfl⟩
    · intro _
      exact List.mem_ofFn.mpr ⟨q x, hright x⟩
  have hmap := hperm.map f
  have hsum := bindListSum_eq_of_perm hmap
  simpa [List.map_ofFn, Function.comp_def] using hsum

/-- State-dependent bijective edge views preserve the complete success mass,
including first-hit suffix weights. -/
theorem successMass_edgeReindexedPayloadStep {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (edgeView edgeUnview : A -> Fin n -> Fin n)
    (hleft : forall state edge,
      edgeUnview state (edgeView state edge) = edge)
    (hright : forall state edge,
      edgeView state (edgeUnview state edge) = edge) :
    forall (node : PayloadNode A S F) T,
      successMass (edgeReindexedPayloadStep step edgeView) node T =
        successMass step node T := by
  intro node T
  induction T generalizing node with
  | zero => cases node <;> rfl
  | succ T ih =>
      cases node with
      | success endpoint =>
          rw [successMass_success, successMass_success]
      | failure endpoint =>
          rw [successMass_failure, successMass_failure]
      | active state =>
          simp only [successMass]
          calc
            (List.ofFn (fun edge : Fin n =>
                successMass (edgeReindexedPayloadStep step edgeView)
                  (step state (edgeView state edge)) T)).sum =
                (List.ofFn (fun edge : Fin n =>
                  successMass step
                    (step state (edgeView state edge)) T)).sum :=
              ofFn_sum_eq _ _ (fun edge =>
                ih (step state (edgeView state edge)))
            _ = (List.ofFn (fun edge : Fin n =>
                  successMass step (step state edge) T)).sum :=
              bindFinSum_reindex (edgeView state) (edgeUnview state)
                (hleft state) (hright state)
                (fun edge => successMass step (step state edge) T)

/-- The endpoint-weighted first-terminal fold is invariant under the same
state-dependent bijective edge interpretation. -/
theorem firstTerminalBindMass_edgeReindexedPayloadStep
    {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat)
    (edgeView edgeUnview : A -> Fin n -> Fin n)
    (hleft : forall state edge,
      edgeUnview state (edgeView state edge) = edge)
    (hright : forall state edge,
      edgeView state (edgeUnview state edge) = edge) :
    forall (node : PayloadNode A S F) T,
      firstTerminalBindMass (edgeReindexedPayloadStep step edgeView)
          continuation node T =
        firstTerminalBindMass step continuation node T := by
  intro node T
  induction T generalizing node with
  | zero => cases node <;> simp [firstTerminalBindMass]
  | succ T ih =>
      cases node with
      | success endpoint => simp [firstTerminalBindMass]
      | failure endpoint => simp [firstTerminalBindMass]
      | active state =>
          simp only [firstTerminalBindMass, edgeReindexedPayloadStep]
          calc
            (List.ofFn (fun edge : Fin n =>
                firstTerminalBindMass
                  (edgeReindexedPayloadStep step edgeView) continuation
                  (step state (edgeView state edge)) T)).sum =
                (List.ofFn (fun edge : Fin n =>
                  firstTerminalBindMass step continuation
                    (step state (edgeView state edge)) T)).sum :=
              ofFn_sum_eq _ _ (fun edge =>
                ih (step state (edgeView state edge)))
            _ = (List.ofFn (fun edge : Fin n =>
                  firstTerminalBindMass step continuation
                    (step state edge) T)).sum :=
              bindFinSum_reindex (edgeView state) (edgeUnview state)
                (hleft state) (hright state)
                (fun edge => firstTerminalBindMass step continuation
                  (step state edge) T)

theorem firstTerminalBindMass_congr_continuation
    {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (left right : S -> Nat) (heq : forall endpoint, left endpoint = right endpoint) :
    forall (node : PayloadNode A S F) T,
      firstTerminalBindMass step left node T =
        firstTerminalBindMass step right node T := by
  intro node T
  induction T generalizing node with
  | zero =>
      cases node with
      | active state => rfl
      | failure endpoint => rfl
      | success endpoint => simp [firstTerminalBindMass, heq endpoint]
  | succ T ih =>
      cases node with
      | success endpoint => simp [firstTerminalBindMass, heq endpoint]
      | failure endpoint => rfl
      | active state =>
          simp only [firstTerminalBindMass]
          exact ofFn_sum_eq _ _ (fun edge => ih _)

/-- The endpoint cut is an exact scheduler-edge view: a raw physical edge is
first converted by `cutCoord`, and `cutView_step_at_cutPos` then gives the
literal same protocol interaction in canonical coordinates. -/
theorem cutView_step_at_cutCoord {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (tail : Fin n) (C : Fin n -> State k)
    (rawEdge : Fin n) :
    cutView ring tail
        ((CenteredRenewal.protocol k hk).step ring C rawEdge) =
      (CenteredRenewal.protocol k hk).step ring (cutView ring tail C)
        (cutCoord ring tail rawEdge) := by
  simpa using Rank.cutView_step_at_cutPos hk ring tail C
    (cutCoord ring tail rawEdge)

/-- Reindex a canonical payload machine by the raw physical coordinates of a
specific renewal endpoint. -/
def cutReindexedPayloadStep {A S F : Type} {n : Nat}
    (ring : DirectedRing n) (tail : Fin n)
    (step : A -> Fin n -> PayloadNode A S F) :
    A -> Fin n -> PayloadNode A S F :=
  edgeReindexedPayloadStep step (fun _ rawEdge =>
    cutCoord ring tail rawEdge)

theorem successMass_cutReindexedPayloadStep {A S F : Type} {n : Nat}
    (ring : DirectedRing n) (tail : Fin n)
    (step : A -> Fin n -> PayloadNode A S F)
    (node : PayloadNode A S F) (T : Nat) :
    successMass (cutReindexedPayloadStep ring tail step) node T =
      successMass step node T := by
  simpa [cutReindexedPayloadStep] using
    successMass_edgeReindexedPayloadStep step
      (fun _ rawEdge => cutCoord ring tail rawEdge)
      (fun _ cutEdge => cutPos ring tail cutEdge)
      (fun _ edge => cutPos_cutCoord ring tail edge)
      (fun _ edge => cutCoord_cutPos ring tail edge) node T

theorem firstTerminalBindMass_cutReindexedPayloadStep
    {A S F : Type} {n : Nat}
    (ring : DirectedRing n) (tail : Fin n)
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat) (node : PayloadNode A S F) (T : Nat) :
    firstTerminalBindMass (cutReindexedPayloadStep ring tail step)
        continuation node T =
      firstTerminalBindMass step continuation node T := by
  simpa [cutReindexedPayloadStep] using
    firstTerminalBindMass_edgeReindexedPayloadStep step continuation
      (fun _ rawEdge => cutCoord ring tail rawEdge)
      (fun _ cutEdge => cutPos ring tail cutEdge)
      (fun _ edge => cutPos_cutCoord ring tail edge)
      (fun _ edge => cutCoord_cutPos ring tail edge) node T

/-! ## Fire-to-race endpoint bind -/

/-- A fire drop has already succeeded and therefore admits every race-budget
suffix.  A fired endpoint instead starts the literal physical race immediately
from its stored configuration and certificate. -/
noncomputable def fireContinuation {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    FireSuccess (r := r) hk ring -> Nat
  | .dropped _ _ => n ^ (4 * n ^ 2)
  | .fired _ F hrank =>
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (.active (.active
          (RankBlockRace.FiredRaceState.toBulletRaceState hn3 F hrank)))
        (4 * n ^ 2)

/-- Exact first-terminal fire mass followed by the race mass.  Unused fire
coordinates occur only as the `n^remaining` suffix after the continuation. -/
noncomputable def fireRaceBindMass {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) : Nat :=
  firstTerminalBindMass (firePayloadStep (r := r) hn3 hndvd)
    (fireContinuation (r := r) hn3 hndvd)
    (.active (.active X F hrank)) (2 * n)

theorem fireContinuation_success_quarter {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (endpoint : FireSuccess (r := r) hk ring) :
    n ^ (4 * n ^ 2) <=
      4 * fireContinuation (r := r) hn3 hndvd endpoint := by
  cases endpoint with
  | dropped X rank_lt =>
      simp [fireContinuation]
      omega
  | fired X F hrank =>
      simpa [fireContinuation] using
        firedRace_success_quarter_by_four_mul_sq hn3 hndvd F hrank

/-- The two physical stages after a good renewal retain at least a sixteenth
of all length-`2*n + 4*n^2` continuation words. -/
theorem fireRaceBind_success_sixteenth
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    n ^ ((2 * n) + (4 * n ^ 2)) <=
      16 * fireRaceBindMass hn3 hndvd X F hrank := by
  let fireMass := successMass (firePayloadStep (r := r) hn3 hndvd)
    (.active (.active X F hrank)) (2 * n)
  let bindMass := fireRaceBindMass hn3 hndvd X F hrank
  have hfire : n ^ (2 * n) <= 4 * fireMass := by
    simpa [fireMass] using
      typedFire_success_quarter_by_two_mul hn3 hndvd X F hrank
  have hbind : n ^ (4 * n ^ 2) * fireMass <= 4 * bindMass := by
    simpa [fireMass, bindMass, fireRaceBindMass] using
      successMass_mul_le_firstTerminalBindMass
        (firePayloadStep (r := r) hn3 hndvd)
        (fireContinuation (r := r) hn3 hndvd)
        (fireContinuation_success_quarter hn3 hndvd)
        (.active (.active X F hrank)) (2 * n)
  calc
    n ^ ((2 * n) + (4 * n ^ 2)) =
        n ^ (4 * n ^ 2) * n ^ (2 * n) := by
      rw [Nat.pow_add, Nat.mul_comm]
    _ <= n ^ (4 * n ^ 2) * (4 * fireMass) :=
      Nat.mul_le_mul_left _ hfire
    _ = 4 * (n ^ (4 * n ^ 2) * fireMass) := by ac_rfl
    _ <= 4 * (4 * bindMass) := Nat.mul_le_mul_left 4 hbind
    _ = 16 * bindMass := by omega

/-! ## Raw physical scheduler view at a renewal endpoint -/

/-- The first fire interaction after re-cutting is the same literal physical
interaction selected by the raw edge.  This is the semantic join behind the
finite-sum reindexing below. -/
theorem fireProofState_next_cutCoord_configuration
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (F : FireReady hk ring (cutView ring tail C))
    (hrank : PhiAt ring tail C = r) (rawEdge : Fin n) :
    (FireProofState.next hn3 hndvd
        (.active (cutView ring tail C) F hrank)
        (cutCoord ring tail rawEdge)).configuration =
      cutView ring tail
        ((CenteredRenewal.protocol k hk).step ring C rawEdge) := by
  have hnext := FireProofState.configuration_next hn3 hndvd
    (.active (cutView ring tail C) F hrank)
    (cutCoord ring tail rawEdge) (by rfl)
  rw [hnext]
  exact (cutView_step_at_cutCoord hk ring tail C rawEdge).symm

/-- Race mass with every suffix symbol interpreted in the renewal endpoint's
raw physical coordinates.  The view is endpoint-dependent, but bijective at
every scheduler node. -/
noncomputable def rawFireContinuation {n k r : Nat} {hk : 0 < k}
    (ring : DirectedRing n) (tail : Fin n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    FireSuccess (r := r) hk ring -> Nat
  | .dropped _ _ => n ^ (4 * n ^ 2)
  | .fired _ F hrank =>
      successMass
        (cutReindexedPayloadStep ring tail
          (RaceProofState.payloadStep hn3 hndvd))
        (.active (.active
          (RankBlockRace.FiredRaceState.toBulletRaceState hn3 F hrank)))
        (4 * n ^ 2)

/-- The literal raw-word fire/race composition at one physical renewal
endpoint.  Both stages consume the next symbols of the same suffix word after
the endpoint-tail coordinate view; no extra symbol is inserted at the join. -/
noncomputable def rawFireRaceBindMass {n k r : Nat} {hk : 0 < k}
    (ring : DirectedRing n) (tail : Fin n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) : Nat :=
  firstTerminalBindMass
    (cutReindexedPayloadStep ring tail
      (firePayloadStep (r := r) hn3 hndvd))
    (rawFireContinuation (r := r) ring tail hn3 hndvd)
    (.active (.active X F hrank)) (2 * n)

theorem rawFireContinuation_eq_fireContinuation
    {n k r : Nat} {hk : 0 < k} (ring : DirectedRing n)
    (tail : Fin n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (endpoint : FireSuccess (r := r) hk ring) :
    rawFireContinuation (r := r) ring tail hn3 hndvd endpoint =
      fireContinuation (r := r) hn3 hndvd endpoint := by
  cases endpoint with
  | dropped X rank_lt => rfl
  | fired X F hrank =>
      exact successMass_cutReindexedPayloadStep ring tail
        (RaceProofState.payloadStep hn3 hndvd)
        (.active (.active
          (RankBlockRace.FiredRaceState.toBulletRaceState hn3 F hrank)))
        (4 * n ^ 2)

theorem rawFireRaceBindMass_eq_fireRaceBindMass
    {n k r : Nat} {hk : 0 < k} (ring : DirectedRing n)
    (tail : Fin n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    rawFireRaceBindMass ring tail hn3 hndvd X F hrank =
      fireRaceBindMass hn3 hndvd X F hrank := by
  calc
    rawFireRaceBindMass ring tail hn3 hndvd X F hrank =
        firstTerminalBindMass
          (cutReindexedPayloadStep ring tail
            (firePayloadStep (r := r) hn3 hndvd))
          (fireContinuation (r := r) hn3 hndvd)
          (.active (.active X F hrank)) (2 * n) := by
      unfold rawFireRaceBindMass
      exact firstTerminalBindMass_congr_continuation
        (cutReindexedPayloadStep ring tail
          (firePayloadStep (r := r) hn3 hndvd))
        (rawFireContinuation (r := r) ring tail hn3 hndvd)
        (fireContinuation (r := r) hn3 hndvd)
        (rawFireContinuation_eq_fireContinuation ring tail hn3 hndvd)
        (.active (.active X F hrank)) (2 * n)
    _ = fireRaceBindMass hn3 hndvd X F hrank := by
      exact firstTerminalBindMass_cutReindexedPayloadStep ring tail
        (firePayloadStep (r := r) hn3 hndvd)
        (fireContinuation (r := r) hn3 hndvd)
        (.active (.active X F hrank)) (2 * n)

theorem rawFireRaceBind_success_sixteenth
    {n k r : Nat} {hk : 0 < k} (ring : DirectedRing n)
    (tail : Fin n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    n ^ ((2 * n) + (4 * n ^ 2)) <=
      16 * rawFireRaceBindMass ring tail hn3 hndvd X F hrank := by
  rw [rawFireRaceBindMass_eq_fireRaceBindMass]
  exact fireRaceBind_success_sixteenth hn3 hndvd X F hrank

/-! ## Full renewal-to-fire-to-race bind -/

/-- Continuation attached to the exact first renewal endpoint.  A renewal
drop succeeds immediately.  A good endpoint is re-cut at its stored tail and
starts fire at that exact `cutView`; no scheduler edge is consumed at the
join. -/
noncomputable def renewalContinuation {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (hr1 : 1 < r) : RenewalSuccess (r := r) hk ring -> Nat
  | .dropped _ _ => n ^ ((2 * n) + (4 * n ^ 2))
  | .good state certificate hrank =>
      let G := Classical.choice certificate
      let X := cutView ring state.tail state.config
      let F : FireReady hk ring X :=
        RankBlockTrial.GoodFreshRenewal.toFireReady G (by
        change 1 < PhiAt ring state.tail state.config
        rw [hrank]
        exact hr1)
      rawFireRaceBindMass ring state.tail hn3 hndvd X F (by
        change PhiAt ring state.tail state.config = r
        exact hrank)

/-- Literal nested mass of the complete rank block.  The outer fold stops at
the first renewal terminal, runs its endpoint-dependent continuation, and
only then pads unused renewal coordinates. -/
noncomputable def rankBlockBindMass {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) : Nat :=
  firstTerminalBindMass (renewalPayloadStep (r := r) hn3 hndvd)
    (renewalContinuation (r := r) hn3 hndvd hr1)
    (.active (initialRenewalActive hk ring C tail hone hrank hr1))
    (8 * n ^ 2)

theorem renewalContinuation_success_sixteenth
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (hr1 : 1 < r)
    (endpoint : RenewalSuccess (r := r) hk ring) :
    n ^ ((2 * n) + (4 * n ^ 2)) <=
      16 * renewalContinuation (r := r) hn3 hndvd hr1 endpoint := by
  cases endpoint with
  | dropped state rank_lt =>
      simp [renewalContinuation]
      omega
  | good state certificate hrank =>
      simpa [renewalContinuation] using
        rawFireRaceBind_success_sixteenth ring state.tail hn3 hndvd
          (cutView ring state.tail state.config)
          (RankBlockTrial.GoodFreshRenewal.toFireReady
            (Classical.choice certificate) (by
            change 1 < PhiAt ring state.tail state.config
            rw [hrank]
            exact hr1)) (by
              change PhiAt ring state.tail state.config = r
              exact hrank)

/-- Exact endpoint-preserving rank-block estimate.  The horizon is the raw
sum of the three physical budgets, with no extra transition at either join. -/
theorem rankBlockBind_success_one_over_thirty_two
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ ((8 * n ^ 2) + ((2 * n) + (4 * n ^ 2))) <=
      32 * rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1 := by
  let renewalMass := successMass (renewalPayloadStep (r := r) hn3 hndvd)
    (.active (initialRenewalActive hk ring C tail hone hrank hr1))
    (8 * n ^ 2)
  let bindMass := rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1
  have hrenewal : n ^ (8 * n ^ 2) <= 2 * renewalMass := by
    simpa [renewalMass] using
      initialTypedRenewal_success_half_by_eight_mul_sq
        hk ring hn3 hndvd C tail hone hrank hr1
  have hbind : n ^ ((2 * n) + (4 * n ^ 2)) * renewalMass <=
      16 * bindMass := by
    simpa [renewalMass, bindMass, rankBlockBindMass] using
      successMass_mul_le_firstTerminalBindMass
        (renewalPayloadStep (r := r) hn3 hndvd)
        (renewalContinuation (r := r) hn3 hndvd hr1)
        (renewalContinuation_success_sixteenth hn3 hndvd hr1)
        (.active (initialRenewalActive hk ring C tail hone hrank hr1))
        (8 * n ^ 2)
  calc
    n ^ ((8 * n ^ 2) + ((2 * n) + (4 * n ^ 2))) =
        n ^ ((2 * n) + (4 * n ^ 2)) * n ^ (8 * n ^ 2) := by
      rw [Nat.pow_add, Nat.mul_comm]
    _ <= n ^ ((2 * n) + (4 * n ^ 2)) * (2 * renewalMass) :=
      Nat.mul_le_mul_left _ hrenewal
    _ = 2 * (n ^ ((2 * n) + (4 * n ^ 2)) * renewalMass) := by ac_rfl
    _ <= 2 * (16 * bindMass) := Nat.mul_le_mul_left 2 hbind
    _ = 32 * bindMass := by omega

/-- Arithmetic-normalized form of the exact budget: `12*n^2 + 2*n`. -/
theorem rankBlockBind_success_one_over_thirty_two_exact_horizon
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (12 * n ^ 2 + 2 * n) <=
      32 * rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1 := by
  rw [show 12 * n ^ 2 + 2 * n =
      (8 * n ^ 2) + ((2 * n) + (4 * n ^ 2)) by omega]
  exact rankBlockBind_success_one_over_thirty_two
    hk ring hn3 hndvd C tail hone hrank hr1

/-! ## Conservative block-boundary padding -/

/-- Count the exact successful first-hit cylinders and then append an
arbitrary suffix of length `4*n^2`.  This is counting padding after the whole
continuation; it does not claim that the strict-drop endpoint is absorbing
under those physical suffix interactions. -/
noncomputable def rankBlockBindPaddedMass {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) : Nat :=
  rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1 *
    n ^ (4 * n ^ 2)

/-- Conservative `16*n^2 + 2*n` horizon form.  The extra `4*n^2` symbols are
explicit suffix-cylinder coordinates after the exact `12*n^2+2*n` bind. -/
theorem rankBlockBind_success_one_over_thirty_two_padded_horizon
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (16 * n ^ 2 + 2 * n) <=
      32 * rankBlockBindPaddedMass
        hk ring hn3 hndvd C tail hone hrank hr1 := by
  have hexact := rankBlockBind_success_one_over_thirty_two_exact_horizon
    hk ring hn3 hndvd C tail hone hrank hr1
  have hmul := Nat.mul_le_mul_right (n ^ (4 * n ^ 2)) hexact
  rw [show 16 * n ^ 2 + 2 * n =
      (12 * n ^ 2 + 2 * n) + (4 * n ^ 2) by omega,
    Nat.pow_add]
  simpa [rankBlockBindPaddedMass, Nat.mul_assoc] using hmul

/-! ## Literal non-success endpoint and restart seam -/

/-- Exact physical endpoint carried along a raw scheduler word.  Unlike the
scalar bind, this state never erases the configuration or the moving barrier
witness. -/
structure LiteralOneBarrierState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) where
  config : Fin n -> State k
  barrier : Fin n
  oneBarrier : OneBarrierAt hk ring config barrier

/-- One actual centered protocol interaction, with the barrier witness moved
exactly when the selected physical edge advances it. -/
def LiteralOneBarrierState.next {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralOneBarrierState hk ring) (edge : Fin n) :
    LiteralOneBarrierState hk ring :=
  let D := (CenteredRenewal.protocol k hk).step ring state.config edge
  let nextBarrier := if CenteredRenewal.AdvanceReady hk ring state.config edge
    then ring.rightNeighbor state.barrier else state.barrier
  ⟨D, nextBarrier,
    (Rank.oneBarrier_phi_step_le hk ring hn3 state.config state.barrier
      edge hndvd state.oneBarrier).1⟩

theorem LiteralOneBarrierState.next_rank_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralOneBarrierState hk ring) (edge : Fin n) :
    PhiAt ring (state.next hn3 hndvd edge).barrier
        (state.next hn3 hndvd edge).config <=
      PhiAt ring state.barrier state.config := by
  simpa [LiteralOneBarrierState.next] using
    (Rank.oneBarrier_phi_step_le hk ring hn3 state.config state.barrier
      edge hndvd state.oneBarrier).2

/-- Execute a literal raw scheduler word, preserving its actual endpoint. -/
def LiteralOneBarrierState.run {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    LiteralOneBarrierState hk ring -> List (Fin n) ->
      LiteralOneBarrierState hk ring
  | state, [] => state
  | state, edge :: suffix =>
      (state.next hn3 hndvd edge).run hn3 hndvd suffix

theorem LiteralOneBarrierState.run_rank_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralOneBarrierState hk ring) : forall word : List (Fin n),
    let endpoint := state.run hn3 hndvd word
    PhiAt ring endpoint.barrier endpoint.config <=
      PhiAt ring state.barrier state.config := by
  intro word
  induction word generalizing state with
  | nil => exact Nat.le_refl _
  | cons edge suffix ih =>
      exact Nat.le_trans (ih (state.next hn3 hndvd edge))
        (state.next_rank_le hn3 hndvd edge)

def initialLiteralOneBarrierState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) : LiteralOneBarrierState hk ring where
  config := C
  barrier := tail
  oneBarrier := hone

/-- Every raw scheduler word which has not strictly lowered rank ends at an
actual restart state: its literal endpoint still has exactly one barrier and
has rank exactly the starting plateau rank.  This is the endpoint-retaining
non-success seam needed at any fixed block boundary. -/
theorem literalWord_nonDrop_endpoint_restart
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (word : List (Fin n))
    (hnotdrop : ¬ PhiAt ring
      ((initialLiteralOneBarrierState hk ring C tail hone).run
        hn3 hndvd word).barrier
      ((initialLiteralOneBarrierState hk ring C tail hone).run
        hn3 hndvd word).config < r) :
    let endpoint := (initialLiteralOneBarrierState hk ring C tail hone).run
      hn3 hndvd word
    OneBarrierAt hk ring endpoint.config endpoint.barrier ∧
      PhiAt ring endpoint.barrier endpoint.config = r := by
  let start := initialLiteralOneBarrierState hk ring C tail hone
  let endpoint := start.run hn3 hndvd word
  have hleStart := start.run_rank_le hn3 hndvd word
  have hle : PhiAt ring endpoint.barrier endpoint.config <= r := by
    calc
      PhiAt ring endpoint.barrier endpoint.config <=
          PhiAt ring start.barrier start.config := hleStart
      _ = r := by simpa [start, initialLiteralOneBarrierState] using hrank
  have heq : PhiAt ring endpoint.barrier endpoint.config = r :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnotdrop)
  exact ⟨endpoint.oneBarrier, heq⟩

/-- Fixed conservative block-boundary specialization.  The length premise
identifies the `16*n^2+2*n` block; the conclusion retains the actual endpoint
configuration rather than a unit failure marker. -/
theorem paddedRankBlock_nonDrop_endpoint_restart
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (word : List (Fin n)) (_wordLength : word.length = 16 * n ^ 2 + 2 * n)
    (hnotdrop : ¬ PhiAt ring
      ((initialLiteralOneBarrierState hk ring C tail hone).run
        hn3 hndvd word).barrier
      ((initialLiteralOneBarrierState hk ring C tail hone).run
        hn3 hndvd word).config < r) :
    let endpoint := (initialLiteralOneBarrierState hk ring C tail hone).run
      hn3 hndvd word
    OneBarrierAt hk ring endpoint.config endpoint.barrier ∧
      PhiAt ring endpoint.barrier endpoint.config = r := by
  exact literalWord_nonDrop_endpoint_restart
    hk ring hn3 hndvd C tail hone hrank word hnotdrop

/-! ## Literal raw hit-count bridge -/

/-- Boolean event used by the global finite-scheduler recurrence: the literal
physical configuration has a one-barrier witness whose cut rank is below the
fixed block rank. -/
def physicalRankDropTest {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (r : Nat) (C : Fin n -> State k) : Bool :=
  decide (∃ barrier : Fin n,
    OneBarrierAt hk ring C barrier ∧ PhiAt ring barrier C < r)

@[simp] theorem physicalRankDropTest_eq_true_iff
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (r : Nat)
    (C : Fin n -> State k) :
    physicalRankDropTest hk ring r C = true ↔
      ∃ barrier : Fin n,
        OneBarrierAt hk ring C barrier ∧ PhiAt ring barrier C < r := by
  simp [physicalRankDropTest]

theorem physicalRankDropTest_at_oneBarrier
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier) :
    physicalRankDropTest hk ring r C = true ↔
      PhiAt ring barrier C < r := by
  rw [physicalRankDropTest_eq_true_iff]
  constructor
  · rintro ⟨other, hother, hdrop⟩
    have hotherEq : other = barrier := by
      apply (hone other).1
      exact oneBarrierAt_barrier hk ring C other hother
    simpa [hotherEq] using hdrop
  · intro hdrop
    exact ⟨barrier, hone, hdrop⟩

/-- If a local Boolean event already holds, every word of the remaining
horizon is a hit. -/
theorem localHitCount_of_post_true {Q : Type} {n : Nat}
    (ring : DirectedRing n) (transition : Q -> Q -> Q × Q)
    (post : (Fin n -> Q) -> Bool) (C : Fin n -> Q)
    (T : Nat) (hpost : post C = true) :
    localHitCount ring transition post C T = n ^ T := by
  unfold localHitCount
  rw [List.countP_eq_length.mpr, allSchedules_length]
  intro word _
  cases word <;> simp [hitsWithinLocal, hpost]

/-- With a false initial event, the exact raw hit count splits over the first
physical scheduler edge. -/
theorem localHitCount_succ_of_post_false {Q : Type} {n : Nat}
    (ring : DirectedRing n) (transition : Q -> Q -> Q × Q)
    (post : (Fin n -> Q) -> Bool) (C : Fin n -> Q)
    (T : Nat) (hpost : post C = false) :
    localHitCount ring transition post C (T + 1) =
      (List.ofFn (fun edge : Fin n =>
        localHitCount ring transition post
          (localStep ring transition C edge) T)).sum := by
  unfold localHitCount
  rw [show T + 1 = 1 + T by omega, allSchedules_add,
    List.countP_flatMap]
  have hone : allSchedules n 1 =
      List.ofFn (fun edge : Fin n => [edge]) := by
    simp [allSchedules]
  rw [hone, List.map_ofFn]
  apply ofFn_sum_eq
  intro edge
  change ((allSchedules n T).map
      (fun suffix => [edge] ++ suffix)).countP
        (hitsWithinLocal ring transition post C) =
    (allSchedules n T).countP
      (hitsWithinLocal ring transition post
        (localStep ring transition C edge))
  rw [List.countP_map]
  apply congrArg (fun predicate => (allSchedules n T).countP predicate)
  funext suffix
  simp [Function.comp_apply, hitsWithinLocal, hpost]

/-- Exact physical/canonical frame transport for one raw edge.  The cut edge
fed to a canonical proof machine is state-dependent, and the output view is
re-cut at the actual successor barrier. -/
theorem cutSuccessor_cutView_at_cutCoord
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (barrier rawEdge : Fin n) :
    let D := (CenteredRenewal.protocol k hk).step ring C rawEdge
    let nextBarrier :=
      if CenteredRenewal.AdvanceReady hk ring C rawEdge
      then ring.rightNeighbor barrier else barrier
    Rank.cutSuccessor hk ring (cutView ring barrier C)
        (cutCoord ring barrier rawEdge) =
      cutView ring nextBarrier D := by
  let D := (CenteredRenewal.protocol k hk).step ring C rawEdge
  let cutEdge := cutCoord ring barrier rawEdge
  have hview :
      (CenteredRenewal.protocol k hk).step ring (cutView ring barrier C)
          cutEdge = cutView ring barrier D := by
    funext i
    exact congrFun
      (cutView_step_at_cutCoord hk ring barrier C rawEdge).symm i
  have hreadyIff :
      CenteredRenewal.AdvanceReady hk ring (cutView ring barrier C) cutEdge ↔
        CenteredRenewal.AdvanceReady hk ring C rawEdge := by
    change IsBarrier hk (C (cutPos ring barrier cutEdge))
        (C (cutPos ring barrier (ring.rightNeighbor cutEdge))) ∧
        (C (cutPos ring barrier cutEdge)).phase = true ↔
      IsBarrier hk (C rawEdge) (C (ring.rightNeighbor rawEdge)) ∧
        (C rawEdge).phase = true
    rw [cutPos_rightNeighbor, cutPos_cutCoord]
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C rawEdge
  · have hreadyCut := hreadyIff.2 hready
    simp only [hready, if_true]
    change Rank.cutSuccessor hk ring (cutView ring barrier C) cutEdge =
      cutView ring (ring.rightNeighbor barrier) D
    rw [show Rank.cutSuccessor hk ring (cutView ring barrier C) cutEdge =
        rotateCut ring
          ((CenteredRenewal.protocol k hk).step ring
            (cutView ring barrier C) cutEdge) by
      simp [Rank.cutSuccessor, hreadyCut]]
    rw [hview]
    exact (cutView_nextBarrier ring barrier D).symm
  · have hreadyCut :
        ¬ CenteredRenewal.AdvanceReady hk ring
          (cutView ring barrier C) cutEdge :=
      fun h => hready (hreadyIff.1 h)
    simp only [hready, if_false]
    change Rank.cutSuccessor hk ring (cutView ring barrier C) cutEdge =
      cutView ring barrier D
    rw [show Rank.cutSuccessor hk ring (cutView ring barrier C) cutEdge =
        (CenteredRenewal.protocol k hk).step ring
          (cutView ring barrier C) cutEdge by
      unfold Rank.cutSuccessor
      simp only [hreadyCut]
      funext j
      rfl]
    funext i
    exact congrFun hview i

/-- The endpoint-carrying canonical race mass injects into the literal raw
physical hit count.  At every active node the raw edge is reindexed by the
current physical barrier, so barrier advances update the view rather than
silently reusing the old cut numeral. -/
theorem raceSuccessMass_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (z : RaceProofState hk ring r)
    (hview : z.configuration = cutView ring barrier C) : forall T,
    successMass (RaceProofState.payloadStep hn3 hndvd) z.payloadNode T <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C T := by
  intro T
  induction T generalizing C barrier z with
  | zero =>
      cases z with
      | active state =>
          simp [RaceProofState.payloadNode, successMass]
      | failure X =>
          simp [RaceProofState.payloadNode]
      | success X rank_lt =>
          have hdrop : PhiAt ring barrier C < r := by
            change Phi (cutView ring barrier C) < r
            rw [← hview]
            exact rank_lt
          have hpost :=
            (physicalRankDropTest_at_oneBarrier C barrier hone).2 hdrop
          rw [localHitCount_of_post_true ring
            (CenteredRenewal.transition hk)
            (physicalRankDropTest hk ring r) C 0 hpost]
          exact Nat.le_refl _
  | succ T ih =>
      cases z with
      | failure X =>
          simp only [RaceProofState.payloadNode, successMass_failure]
          exact Nat.zero_le _
      | success X rank_lt =>
          have hdrop : PhiAt ring barrier C < r := by
            change Phi (cutView ring barrier C) < r
            rw [← hview]
            exact rank_lt
          have hpost :=
            (physicalRankDropTest_at_oneBarrier C barrier hone).2 hdrop
          simp only [RaceProofState.payloadNode, successMass_success]
          rw [
            localHitCount_of_post_true ring
              (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) C (T + 1) hpost]
          exact Nat.le_refl _
      | active state =>
          have hrankPhysical : PhiAt ring barrier C = r := by
            change Phi (cutView ring barrier C) = r
            rw [← hview]
            exact state.rank_eq
          have hpostFalse : physicalRankDropTest hk ring r C = false := by
            cases hpost : physicalRankDropTest hk ring r C with
            | false => rfl
            | true =>
                have hdrop :=
                  (physicalRankDropTest_at_oneBarrier C barrier hone).1 hpost
                omega
          rw [localHitCount_succ_of_post_false ring
            (CenteredRenewal.transition hk)
            (physicalRankDropTest hk ring r) C T hpostFalse]
          simp only [RaceProofState.payloadNode, successMass,
            PayloadFiniteStoppingTree.stepNode]
          let canonicalChildMass : Fin n -> Nat := fun cutEdge =>
            successMass (RaceProofState.payloadStep hn3 hndvd)
              (RaceProofState.payloadStep hn3 hndvd (.active state) cutEdge) T
          calc
            (List.ofFn canonicalChildMass).sum =
                (List.ofFn (fun rawEdge : Fin n =>
                  canonicalChildMass (cutCoord ring barrier rawEdge))).sum := by
              symm
              exact bindFinSum_reindex
                (cutCoord ring barrier) (cutPos ring barrier)
                (cutPos_cutCoord ring barrier)
                (cutCoord_cutPos ring barrier) canonicalChildMass
            _ <= (List.ofFn (fun rawEdge : Fin n =>
                localHitCount ring (CenteredRenewal.transition hk)
                  (physicalRankDropTest hk ring r)
                  (localStep ring (CenteredRenewal.transition hk) C rawEdge)
                  T)).sum := by
              apply ofFn_sum_le
              intro rawEdge
              let D := (CenteredRenewal.protocol k hk).step ring C rawEdge
              let nextBarrier :=
                if CenteredRenewal.AdvanceReady hk ring C rawEdge
                then ring.rightNeighbor barrier else barrier
              let cutEdge := cutCoord ring barrier rawEdge
              let next := RaceProofState.next hn3 hndvd
                (.active state) cutEdge
              have honeNext : OneBarrierAt hk ring D nextBarrier := by
                exact (Rank.oneBarrier_phi_step_le hk ring hn3 C barrier
                  rawEdge hndvd hone).1
              have hnextView : next.configuration =
                  cutView ring nextBarrier D := by
                change state.race.config = cutView ring barrier C at hview
                calc
                  next.configuration = Rank.cutSuccessor hk ring
                      state.race.config cutEdge :=
                    RaceProofState.configuration_next hn3 hndvd
                      (.active state) cutEdge (by rfl)
                  _ = Rank.cutSuccessor hk ring
                      (cutView ring barrier C) cutEdge :=
                    congrArg (fun X =>
                      Rank.cutSuccessor hk ring X cutEdge) hview
                  _ = cutView ring nextBarrier D := by
                    exact cutSuccessor_cutView_at_cutCoord
                      hk ring C barrier rawEdge
              have hchild := ih D nextBarrier honeNext next hnextView
              change successMass (RaceProofState.payloadStep hn3 hndvd)
                  (RaceProofState.payloadStep hn3 hndvd
                    (.active state) cutEdge) T <= _
              rw [show localStep ring (CenteredRenewal.transition hk) C rawEdge =
                  D by
                exact localStep_eq_protocol_step
                  (CenteredRenewal.protocol k hk) ring C rawEdge]
              simpa [canonicalChildMass, RaceProofState.payloadStep, next]
                using hchild

/-! ## Literal fire/race bridge -/

/-- Regard every total fire proof state as the corresponding typed payload
node.  This makes the endpoint retained by `FireProofState.next` available to
the physical-word induction below. -/
def firePayloadNode {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireProofState hk ring r ->
    PayloadNode (FireProofState hk ring r)
      (FireSuccess (r := r) hk ring) (FireFailure (k := k) ring)
  | s@(.active _ _ _) => .active s
  | .fired X F hrank => .success (.fired X F hrank)
  | .dropped X rank_lt => .success (.dropped X rank_lt)
  | .missed X => .failure ⟨X⟩

@[simp] theorem firePayloadStep_eq_firePayloadNode_next
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (edge : Fin n) :
    firePayloadStep (r := r) hn3 hndvd s edge =
      firePayloadNode (s.next hn3 hndvd edge) := by
  unfold firePayloadStep
  cases s.next hn3 hndvd edge <;> rfl

def FireSuccess.configuration {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireSuccess (r := r) hk ring ->
      Fin n -> State k
  | .fired X _ _ => X
  | .dropped X _ => X

theorem FiredRaceState.toBulletRaceState_configuration
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) {X : Fin n -> State k}
    (F : FiredRaceState hk ring X) (hrank : Phi X = r) :
    (RankBlockRace.FiredRaceState.toBulletRaceState
      hn3 F hrank).race.config = X := by
  rcases F with
    ⟨S, rfl, hholder, htailLeader, htailBullet, htailProbe,
      htailPhase, corridor⟩
  rfl

/-- During the fresh-fire stage the canonical barrier cannot advance: its
phase is zero.  Thus the endpoint stored by the fire machine is also its
literal `cutSuccessor`, which is the form needed by the moving physical
frame. -/
theorem FireProofState.configuration_next_eq_cutSuccessor
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (edge : Fin n)
    (hactive : s.isActive = true) :
    (s.next hn3 hndvd edge).configuration =
      Rank.cutSuccessor hk ring s.configuration edge := by
  cases s with
  | fired X F hrank => simp [FireProofState.isActive] at hactive
  | dropped X rank_lt => simp [FireProofState.isActive] at hactive
  | missed X => simp [FireProofState.isActive] at hactive
  | active X F hrank =>
      change (FireProofState.next hn3 hndvd
        (.active X F hrank) edge).configuration =
          Rank.cutSuccessor hk ring X edge
      have hbarrier : CanonicalOneBarrier hk ring X := by
        simpa [F.config_eq] using F.race.barrier
      have hnotready :
          ¬ CenteredRenewal.AdvanceReady hk ring X edge := by
        intro hready
        have hedge : edge = tailCoord ring :=
          (hbarrier edge).1 hready.1
        subst edge
        have hphase := hready.2
        rw [F.tailPhase] at hphase
        contradiction
      rw [FireProofState.configuration_next hn3 hndvd
        (.active X F hrank) edge (by rfl)]
      unfold Rank.cutSuccessor
      simp only [hnotready]
      funext i
      rfl

/-- A terminal fire payload, followed immediately by its race continuation
and then by arbitrary unused fire coordinates, injects into literal physical
rank-drop words from the exact terminal configuration. -/
theorem fireContinuation_mul_pow_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (endpoint : FireSuccess (r := r) hk ring)
    (hview : endpoint.configuration = cutView ring barrier C)
    (padding : Nat) :
    n ^ padding * fireContinuation (r := r) hn3 hndvd endpoint <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C
        (padding + 4 * n ^ 2) := by
  cases endpoint with
  | dropped X rank_lt =>
      have hdrop : PhiAt ring barrier C < r := by
        change Phi (cutView ring barrier C) < r
        rw [← hview]
        exact rank_lt
      have hpost :=
        (physicalRankDropTest_at_oneBarrier C barrier hone).2 hdrop
      rw [localHitCount_of_post_true ring
        (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C
        (padding + 4 * n ^ 2) hpost]
      simp [fireContinuation, Nat.pow_add]
  | fired X F hrank =>
      let raceState : RaceProofState hk ring r :=
        .active
          (RankBlockRace.FiredRaceState.toBulletRaceState hn3 F hrank)
      have hrace : successMass
          (RaceProofState.payloadStep hn3 hndvd) raceState.payloadNode
          (4 * n ^ 2) <=
          localHitCount ring (CenteredRenewal.transition hk)
            (physicalRankDropTest hk ring r) C (4 * n ^ 2) := by
        apply raceSuccessMass_le_literalRankDropHitCount
          hn3 hndvd C barrier hone raceState
        have hRaceConfig :
            (RankBlockRace.FiredRaceState.toBulletRaceState
              hn3 F hrank).race.config = X :=
          FiredRaceState.toBulletRaceState_configuration hn3 F hrank
        exact hRaceConfig.trans hview
      have hpad := localHitCount_mul_pow_le_add ring
        (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C (4 * n ^ 2) padding
      calc
        n ^ padding * fireContinuation (r := r) hn3 hndvd
            (.fired X F hrank) =
            successMass (RaceProofState.payloadStep hn3 hndvd)
                raceState.payloadNode (4 * n ^ 2) * n ^ padding := by
              simp [fireContinuation, raceState,
                RaceProofState.payloadNode, Nat.mul_comm]
        _ <= localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) C (4 * n ^ 2) *
              n ^ padding := Nat.mul_le_mul_right _ hrace
        _ <= localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) C
              (4 * n ^ 2 + padding) := hpad
        _ = localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) C
              (padding + 4 * n ^ 2) := by
                congr 1
                omega

/-- The complete typed fire/race bind is bounded by the literal raw-word hit
count.  Canonical fire edges are pulled back through the current physical cut;
after each physical interaction the barrier frame is updated before the
induction continues. -/
theorem fireRaceBindFromState_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (s : FireProofState hk ring r)
    (hview : s.configuration = cutView ring barrier C) : forall T,
    firstTerminalBindMass (firePayloadStep (r := r) hn3 hndvd)
        (fireContinuation (r := r) hn3 hndvd) (firePayloadNode s) T <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C (T + 4 * n ^ 2) := by
  intro T
  induction T generalizing C barrier s with
  | zero =>
      cases s with
      | active X F hrank =>
          simp [firePayloadNode, firstTerminalBindMass]
      | missed X =>
          simp [firePayloadNode, firstTerminalBindMass]
      | fired X F hrank =>
          simpa [firePayloadNode, firstTerminalBindMass,
            FireProofState.configuration, FireSuccess.configuration] using
            fireContinuation_mul_pow_le_literalRankDropHitCount
              hn3 hndvd C barrier hone (.fired X F hrank) hview 0
      | dropped X rank_lt =>
          simpa [firePayloadNode, firstTerminalBindMass,
            FireProofState.configuration, FireSuccess.configuration] using
            fireContinuation_mul_pow_le_literalRankDropHitCount
              hn3 hndvd C barrier hone (.dropped X rank_lt) hview 0
  | succ T ih =>
      cases s with
      | missed X =>
          simp [firePayloadNode, firstTerminalBindMass]
      | fired X F hrank =>
          simpa [firePayloadNode, firstTerminalBindMass,
            FireProofState.configuration, FireSuccess.configuration] using
            fireContinuation_mul_pow_le_literalRankDropHitCount
              hn3 hndvd C barrier hone (.fired X F hrank) hview (T + 1)
      | dropped X rank_lt =>
          simpa [firePayloadNode, firstTerminalBindMass,
            FireProofState.configuration, FireSuccess.configuration] using
            fireContinuation_mul_pow_le_literalRankDropHitCount
              hn3 hndvd C barrier hone (.dropped X rank_lt) hview (T + 1)
      | active X F hrank =>
          change X = cutView ring barrier C at hview
          have hrankPhysical : PhiAt ring barrier C = r := by
            change Phi (cutView ring barrier C) = r
            rw [← hview]
            exact hrank
          have hpostFalse : physicalRankDropTest hk ring r C = false := by
            cases hpost : physicalRankDropTest hk ring r C with
            | false => rfl
            | true =>
                have hdrop :=
                  (physicalRankDropTest_at_oneBarrier C barrier hone).1 hpost
                omega
          rw [show (T + 1) + 4 * n ^ 2 =
              (T + 4 * n ^ 2) + 1 by omega,
            localHitCount_succ_of_post_false ring
              (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) C
              (T + 4 * n ^ 2) hpostFalse]
          simp only [firePayloadNode, firstTerminalBindMass]
          let canonicalChildMass : Fin n -> Nat := fun cutEdge =>
            firstTerminalBindMass
              (firePayloadStep (r := r) hn3 hndvd)
              (fireContinuation (r := r) hn3 hndvd)
              (firePayloadStep (r := r) hn3 hndvd
                (.active X F hrank) cutEdge) T
          calc
            (List.ofFn canonicalChildMass).sum =
                (List.ofFn (fun rawEdge : Fin n =>
                  canonicalChildMass
                    (cutCoord ring barrier rawEdge))).sum := by
              symm
              exact bindFinSum_reindex
                (cutCoord ring barrier) (cutPos ring barrier)
                (cutPos_cutCoord ring barrier)
                (cutCoord_cutPos ring barrier) canonicalChildMass
            _ <= (List.ofFn (fun rawEdge : Fin n =>
                localHitCount ring (CenteredRenewal.transition hk)
                  (physicalRankDropTest hk ring r)
                  (localStep ring (CenteredRenewal.transition hk) C rawEdge)
                  (T + 4 * n ^ 2))).sum := by
              apply ofFn_sum_le
              intro rawEdge
              let D := (CenteredRenewal.protocol k hk).step ring C rawEdge
              let nextBarrier :=
                if CenteredRenewal.AdvanceReady hk ring C rawEdge
                then ring.rightNeighbor barrier else barrier
              let cutEdge := cutCoord ring barrier rawEdge
              let next := FireProofState.next hn3 hndvd
                (.active X F hrank) cutEdge
              have honeNext : OneBarrierAt hk ring D nextBarrier := by
                exact (Rank.oneBarrier_phi_step_le hk ring hn3 C barrier
                  rawEdge hndvd hone).1
              have hnextView : next.configuration =
                  cutView ring nextBarrier D := by
                calc
                  next.configuration = Rank.cutSuccessor hk ring X cutEdge :=
                    FireProofState.configuration_next_eq_cutSuccessor
                      hn3 hndvd (.active X F hrank) cutEdge (by rfl)
                  _ = Rank.cutSuccessor hk ring
                      (cutView ring barrier C) cutEdge :=
                    congrArg (fun Y =>
                      Rank.cutSuccessor hk ring Y cutEdge) hview
                  _ = cutView ring nextBarrier D :=
                    cutSuccessor_cutView_at_cutCoord
                      hk ring C barrier rawEdge
              have hchild := ih D nextBarrier honeNext next hnextView
              rw [show localStep ring (CenteredRenewal.transition hk)
                    C rawEdge = D by
                exact localStep_eq_protocol_step
                  (CenteredRenewal.protocol k hk) ring C rawEdge]
              simpa [canonicalChildMass, next] using hchild

theorem fireRaceBindMass_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) (hview : X = cutView ring barrier C) :
    fireRaceBindMass hn3 hndvd X F hrank <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C
        ((2 * n) + (4 * n ^ 2)) := by
  simpa [fireRaceBindMass, firePayloadNode] using
    fireRaceBindFromState_le_literalRankDropHitCount
      hn3 hndvd C barrier hone (.active X F hrank) hview (2 * n)

/-! ## Literal renewal/fire/race bridge -/

def RenewalSuccess.proofState {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RenewalSuccess (r := r) hk ring ->
      RenewalProofState (r := r) hk ring
  | .dropped state _ => state
  | .good state _ _ => state

def RenewalSuccess.configuration {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (endpoint : RenewalSuccess (r := r) hk ring) :
      Fin n -> State k := endpoint.proofState.config

def RenewalSuccess.tail {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (endpoint : RenewalSuccess (r := r) hk ring) :
      Fin n := endpoint.proofState.tail

/-- A renewal terminal starts its endpoint-dependent continuation immediately;
unused renewal coordinates are counted only after that continuation. -/
theorem renewalContinuation_mul_pow_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (hr1 : 1 < r)
    (endpoint : RenewalSuccess (r := r) hk ring)
    (hone : OneBarrierAt hk ring endpoint.configuration endpoint.tail)
    (padding : Nat) :
    n ^ padding * renewalContinuation (r := r) hn3 hndvd hr1 endpoint <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) endpoint.configuration
        (padding + ((2 * n) + (4 * n ^ 2))) := by
  cases endpoint with
  | dropped state rank_lt =>
      change OneBarrierAt hk ring state.config state.tail at hone
      change n ^ padding *
          renewalContinuation (r := r) hn3 hndvd hr1
            (.dropped state rank_lt) <=
        localHitCount ring (CenteredRenewal.transition hk)
          (physicalRankDropTest hk ring r) state.config
          (padding + ((2 * n) + (4 * n ^ 2)))
      have hpost :=
        (physicalRankDropTest_at_oneBarrier state.config state.tail hone).2
          rank_lt
      rw [localHitCount_of_post_true ring
        (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) state.config
        (padding + ((2 * n) + (4 * n ^ 2))) hpost]
      simp [renewalContinuation, Nat.pow_add]
  | good state certificate hrank =>
      let G := Classical.choice certificate
      let X := cutView ring state.tail state.config
      let F : FireReady hk ring X :=
        RankBlockTrial.GoodFreshRenewal.toFireReady G (by
          change 1 < PhiAt ring state.tail state.config
          rw [hrank]
          exact hr1)
      have hfire : rawFireRaceBindMass ring state.tail hn3 hndvd
            X F (by
              change PhiAt ring state.tail state.config = r
              exact hrank) <=
          localHitCount ring (CenteredRenewal.transition hk)
            (physicalRankDropTest hk ring r) state.config
            ((2 * n) + (4 * n ^ 2)) := by
        rw [rawFireRaceBindMass_eq_fireRaceBindMass]
        exact fireRaceBindMass_le_literalRankDropHitCount
          hn3 hndvd state.config state.tail hone X F
          (by
            change PhiAt ring state.tail state.config = r
            exact hrank) rfl
      have hpad := localHitCount_mul_pow_le_add ring
        (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) state.config
        ((2 * n) + (4 * n ^ 2)) padding
      calc
        n ^ padding * renewalContinuation (r := r) hn3 hndvd hr1
            (.good state certificate hrank) =
            rawFireRaceBindMass ring state.tail hn3 hndvd
              X F (by
                change PhiAt ring state.tail state.config = r
                exact hrank) * n ^ padding := by
              simp [renewalContinuation, G, X, F, Nat.mul_comm]
        _ <= localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) state.config
              ((2 * n) + (4 * n ^ 2)) * n ^ padding :=
            Nat.mul_le_mul_right _ hfire
        _ <= localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) state.config
              (((2 * n) + (4 * n ^ 2)) + padding) := hpad
        _ = localHitCount ring (CenteredRenewal.transition hk)
              (physicalRankDropTest hk ring r) state.config
              (padding + ((2 * n) + (4 * n ^ 2))) := by
                congr 1
                omega

/-- The outer renewal bind is a literal raw-word count.  Renewal itself uses
physical edge coordinates, and both the configuration and moving barrier of
every child are identified with the actual centered protocol successor before
the terminal continuation or recursive branch is used. -/
theorem renewalRankBlockBindFromActive_le_literalRankDropHitCount
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (hr1 : 1 < r)
    (s : RenewalActive (r := r) hk ring) : forall T,
    firstTerminalBindMass (renewalPayloadStep (r := r) hn3 hndvd)
        (renewalContinuation (r := r) hn3 hndvd hr1) (.active s) T <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) s.state.config
        (T + ((2 * n) + (4 * n ^ 2))) := by
  intro T
  induction T generalizing s with
  | zero =>
      simp [firstTerminalBindMass]
  | succ T ih =>
      have hone : OneBarrierAt hk ring s.state.config s.state.tail :=
        s.state.active_oneBarrier s.active
      have hpostFalse :
          physicalRankDropTest hk ring r s.state.config = false := by
        cases hpost : physicalRankDropTest hk ring r s.state.config with
        | false => rfl
        | true =>
            have hdrop :=
              (physicalRankDropTest_at_oneBarrier
                s.state.config s.state.tail hone).1 hpost
            have hrank := s.rank_eq
            omega
      rw [show (T + 1) + ((2 * n) + (4 * n ^ 2)) =
            (T + ((2 * n) + (4 * n ^ 2))) + 1 by omega,
        localHitCount_succ_of_post_false ring
          (CenteredRenewal.transition hk)
          (physicalRankDropTest hk ring r) s.state.config
          (T + ((2 * n) + (4 * n ^ 2))) hpostFalse]
      simp only [firstTerminalBindMass]
      apply ofFn_sum_le
      intro selected
      let D := (CenteredRenewal.protocol k hk).step ring
        s.state.config selected
      let nextTail := postStepBarrier hk ring s.state.config
        s.state.tail selected
      have honeNext : OneBarrierAt hk ring D nextTail := by
        simpa [D, nextTail, postStepBarrier] using
          (Rank.oneBarrier_phi_step_le hk ring hn3 s.state.config
            s.state.tail selected hndvd hone).1
      generalize hchild : s.child hn3 hndvd selected = child
      rcases child with ⟨next, hle⟩
      have hnextRaw :
          renewalProofNext hk ring hn3 hndvd s.state selected = next := by
        have h := congrArg RenewalChild.state hchild
        simpa [RenewalActive.child] using h
      have hconfig : next.config = D := by
        rw [← hnextRaw]
        exact renewalProofNext_configuration hk ring hn3 hndvd
          s.state selected s.active
      have htail : next.tail = nextTail := by
        rw [← hnextRaw]
        exact renewalProofNext_tail hk ring hn3 hndvd
          s.state selected s.active
      rw [show localStep ring (CenteredRenewal.transition hk)
            s.state.config selected = D by
        exact localStep_eq_protocol_step
          (CenteredRenewal.protocol k hk) ring s.state.config selected]
      cases next with
      | first active =>
          let s' : RenewalActive (r := r) hk ring :=
            RenewalActive.ofFirst active
          have htyped : renewalPayloadStep (r := r) hn3 hndvd s selected =
              .active s' := by
            simp [renewalPayloadStep, hchild,
              RenewalChild.payloadNode, s']
          rw [htyped]
          have hrec := ih s'
          simpa [s', RenewalActive.ofFirst, hconfig] using hrec
      | second firstUsed hfirst active hspan =>
          let s' : RenewalActive (r := r) hk ring :=
            RenewalActive.ofSecond firstUsed hfirst active hspan
          have htyped : renewalPayloadStep (r := r) hn3 hndvd s selected =
              .active s' := by
            simp [renewalPayloadStep, hchild,
              RenewalChild.payloadNode, s']
          rw [htyped]
          have hrec := ih s'
          simpa [s', RenewalActive.ofSecond, hconfig] using hrec
      | @good C tail used certificate =>
          change C = D at hconfig
          change tail = nextTail at htail
          have honeEndpoint : OneBarrierAt hk ring C tail := by
            simpa [hconfig, htail] using honeNext
          by_cases hdrop : PhiAt ring tail C < r
          · let endpoint : RenewalSuccess (r := r) hk ring :=
              .dropped (.good used certificate) hdrop
            have htyped : renewalPayloadStep (r := r) hn3 hndvd
                s selected = .success endpoint := by
              simp [renewalPayloadStep, hchild,
                RenewalChild.payloadNode, hdrop, endpoint]
            rw [htyped]
            have hterm :=
              renewalContinuation_mul_pow_le_literalRankDropHitCount
                hn3 hndvd hr1 endpoint honeEndpoint T
            simpa [firstTerminalBindMass, endpoint,
              RenewalSuccess.configuration, RenewalSuccess.tail,
              RenewalSuccess.proofState, RenewalProofState.config,
              hconfig] using hterm
          · have heq : PhiAt ring tail C = r :=
              Nat.le_antisymm hle (Nat.le_of_not_gt hdrop)
            let endpoint : RenewalSuccess (r := r) hk ring :=
              .good (.good used certificate) certificate heq
            have htyped : renewalPayloadStep (r := r) hn3 hndvd
                s selected = .success endpoint := by
              simp [renewalPayloadStep, hchild,
                RenewalChild.payloadNode, hdrop, endpoint]
            rw [htyped]
            have hterm :=
              renewalContinuation_mul_pow_le_literalRankDropHitCount
                hn3 hndvd hr1 endpoint honeEndpoint T
            simpa [firstTerminalBindMass, endpoint,
              RenewalSuccess.configuration, RenewalSuccess.tail,
              RenewalSuccess.proofState, RenewalProofState.config,
              hconfig] using hterm
      | @dropped C tail used rank_lt =>
          change C = D at hconfig
          change tail = nextTail at htail
          let endpoint : RenewalSuccess (r := r) hk ring :=
            .dropped (.dropped used rank_lt) rank_lt
          have htyped : renewalPayloadStep (r := r) hn3 hndvd
              s selected = .success endpoint := by
            simp [renewalPayloadStep, hchild,
              RenewalChild.payloadNode, endpoint]
          rw [htyped]
          have honeEndpoint : OneBarrierAt hk ring C tail := by
            simpa [hconfig, htail] using honeNext
          have hterm :=
            renewalContinuation_mul_pow_le_literalRankDropHitCount
              hn3 hndvd hr1 endpoint honeEndpoint T
          simpa [firstTerminalBindMass, endpoint,
            RenewalSuccess.configuration, RenewalSuccess.tail,
            RenewalSuccess.proofState, RenewalProofState.config,
            hconfig] using hterm

/-- The scalar endpoint-preserving bind mass is an actual subset (with
scheduler multiplicity) of literal raw words that visit rank below `r` within
the exact physical horizon. -/
theorem rankBlockBindMass_le_literalRankDropHitCount
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1 <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C
        ((8 * n ^ 2) + ((2 * n) + (4 * n ^ 2))) := by
  simpa [rankBlockBindMass, initialRenewalActive,
    initialRenewalProofState, RenewalProofState.config] using
      renewalRankBlockBindFromActive_le_literalRankDropHitCount
        hn3 hndvd hr1
        (initialRenewalActive hk ring C tail hone hrank hr1)
        (8 * n ^ 2)

theorem rankBlockBindMass_le_literalRankDropHitCount_exact_horizon
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    rankBlockBindMass hk ring hn3 hndvd C tail hone hrank hr1 <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C (12 * n ^ 2 + 2 * n) := by
  rw [show 12 * n ^ 2 + 2 * n =
      (8 * n ^ 2) + ((2 * n) + (4 * n ^ 2)) by omega]
  exact rankBlockBindMass_le_literalRankDropHitCount
    hk ring hn3 hndvd C tail hone hrank hr1

/-- Conservative fixed-block form: the four-square suffix is appended only
after the complete variable-stopping-time bind.  Historical rank drop makes
all such suffix cylinders successful. -/
theorem rankBlockBindPaddedMass_le_literalRankDropHitCount
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    rankBlockBindPaddedMass hk ring hn3 hndvd C tail hone hrank hr1 <=
      localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C (16 * n ^ 2 + 2 * n) := by
  have hbind := rankBlockBindMass_le_literalRankDropHitCount_exact_horizon
    hk ring hn3 hndvd C tail hone hrank hr1
  have hmul := Nat.mul_le_mul_right (n ^ (4 * n ^ 2)) hbind
  have hpad := localHitCount_mul_pow_le_add ring
    (CenteredRenewal.transition hk)
    (physicalRankDropTest hk ring r) C
    (12 * n ^ 2 + 2 * n) (4 * n ^ 2)
  calc
    rankBlockBindPaddedMass hk ring hn3 hndvd C tail hone hrank hr1 <=
        localHitCount ring (CenteredRenewal.transition hk)
          (physicalRankDropTest hk ring r) C
          (12 * n ^ 2 + 2 * n) * n ^ (4 * n ^ 2) := by
      simpa [rankBlockBindPaddedMass] using hmul
    _ <= localHitCount ring (CenteredRenewal.transition hk)
          (physicalRankDropTest hk ring r) C
          ((12 * n ^ 2 + 2 * n) + (4 * n ^ 2)) := hpad
    _ = localHitCount ring (CenteredRenewal.transition hk)
          (physicalRankDropTest hk ring r) C
          (16 * n ^ 2 + 2 * n) := by
      congr 1
      omega

/-- Denominator-cleared literal fixed-block descent probability. -/
theorem literalRankDropHitCount_one_over_thirty_two_padded_horizon
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (16 * n ^ 2 + 2 * n) <=
      32 * localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C (16 * n ^ 2 + 2 * n) := by
  exact Nat.le_trans
    (rankBlockBind_success_one_over_thirty_two_padded_horizon
      hk ring hn3 hndvd C tail hone hrank hr1)
    (Nat.mul_le_mul_left 32
      (rankBlockBindPaddedMass_le_literalRankDropHitCount
        hk ring hn3 hndvd C tail hone hrank hr1))

/-! ## Historical hit equals literal final-endpoint drop -/

/-- Count raw words whose actual physical endpoint, after every scheduled
interaction has run, has one-barrier rank below `r`. -/
def literalPhiDropMass {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (r : Nat) (C : Fin n -> State k)
    (T : Nat) : Nat :=
  (allSchedules n T).countP (fun word =>
    physicalRankDropTest hk ring r
      (runLocalSchedule ring (CenteredRenewal.transition hk) C word))

/-- A physical strict rank drop persists across the next literal interaction.
The successor barrier is the actual moving one-barrier witness. -/
theorem physicalRankDropTest_localStep_of_true
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (hpost : physicalRankDropTest hk ring r C = true)
    (edge : Fin n) :
    physicalRankDropTest hk ring r
      (localStep ring (CenteredRenewal.transition hk) C edge) = true := by
  let D := (CenteredRenewal.protocol k hk).step ring C edge
  let nextBarrier :=
    if CenteredRenewal.AdvanceReady hk ring C edge
    then ring.rightNeighbor barrier else barrier
  have hstep := Rank.oneBarrier_phi_step_le hk ring hn3 C barrier
    edge hndvd hone
  have honeNext : OneBarrierAt hk ring D nextBarrier := hstep.1
  have hle : PhiAt ring nextBarrier D <= PhiAt ring barrier C := hstep.2
  have hdrop := (physicalRankDropTest_at_oneBarrier C barrier hone).1 hpost
  have hdropNext : PhiAt ring nextBarrier D < r :=
    Nat.lt_of_le_of_lt hle hdrop
  rw [show localStep ring (CenteredRenewal.transition hk) C edge = D by
    exact localStep_eq_protocol_step
      (CenteredRenewal.protocol k hk) ring C edge]
  exact (physicalRankDropTest_at_oneBarrier D nextBarrier honeNext).2
    hdropNext

/-- Consequently, a rank drop persists through every unused raw-word suffix;
this is endpoint transport, not an absorbing modification of the protocol. -/
theorem physicalRankDropTest_runLocalSchedule_of_true
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (hpost : physicalRankDropTest hk ring r C = true) :
    forall word : List (Fin n),
    physicalRankDropTest hk ring r
      (runLocalSchedule ring (CenteredRenewal.transition hk) C word) =
        true := by
  intro word
  induction word generalizing C barrier with
  | nil => exact hpost
  | cons edge suffix ih =>
      let D := localStep ring (CenteredRenewal.transition hk) C edge
      let nextBarrier :=
        if CenteredRenewal.AdvanceReady hk ring C edge
        then ring.rightNeighbor barrier else barrier
      have honeNext : OneBarrierAt hk ring D nextBarrier := by
        rw [show D = (CenteredRenewal.protocol k hk).step ring C edge by
          exact localStep_eq_protocol_step
            (CenteredRenewal.protocol k hk) ring C edge]
        exact (Rank.oneBarrier_phi_step_le hk ring hn3 C barrier
          edge hndvd hone).1
      have hpostNext : physicalRankDropTest hk ring r D = true :=
        physicalRankDropTest_localStep_of_true
          hn3 hndvd C barrier hone hpost edge
      exact ih D nextBarrier honeNext hpostNext

/-- On one-barrier physical executions, visiting strict lower rank is
equivalent to ending the complete raw word at strict lower rank. -/
theorem hitsWithinLocal_eq_final_physicalRankDropTest
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier) : forall word : List (Fin n),
    hitsWithinLocal ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C word =
      physicalRankDropTest hk ring r
        (runLocalSchedule ring (CenteredRenewal.transition hk) C word) := by
  intro word
  induction word generalizing C barrier with
  | nil => rfl
  | cons edge suffix ih =>
      let D := localStep ring (CenteredRenewal.transition hk) C edge
      let nextBarrier :=
        if CenteredRenewal.AdvanceReady hk ring C edge
        then ring.rightNeighbor barrier else barrier
      have honeNext : OneBarrierAt hk ring D nextBarrier := by
        rw [show D = (CenteredRenewal.protocol k hk).step ring C edge by
          exact localStep_eq_protocol_step
            (CenteredRenewal.protocol k hk) ring C edge]
        exact (Rank.oneBarrier_phi_step_le hk ring hn3 C barrier
          edge hndvd hone).1
      have ihNext := ih D nextBarrier honeNext
      simp only [hitsWithinLocal, runLocalSchedule]
      rw [ihNext]
      cases hpost : physicalRankDropTest hk ring r C with
      | false =>
          simp only [Bool.false_or]
          rfl
      | true =>
          have hfinal := physicalRankDropTest_runLocalSchedule_of_true
            hn3 hndvd C barrier hone hpost (edge :: suffix)
          simp only [runLocalSchedule] at hfinal
          simp only [Bool.true_or]
          exact hfinal.symm

/-- Exact equality of multiplicity-sensitive counts: no scheduler word is
created or discarded when the historical event is transported to the actual
fixed-horizon endpoint. -/
theorem localHitCount_eq_literalPhiDropMass
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (barrier : Fin n)
    (hone : OneBarrierAt hk ring C barrier) (T : Nat) :
    localHitCount ring (CenteredRenewal.transition hk)
        (physicalRankDropTest hk ring r) C T =
      literalPhiDropMass hk ring r C T := by
  unfold localHitCount literalPhiDropMass
  apply congrArg (fun predicate => (allSchedules n T).countP predicate)
  funext word
  exact hitsWithinLocal_eq_final_physicalRankDropTest
    hn3 hndvd C barrier hone word

/-- Public fixed-block physical bridge requested by the descent recurrence:
every scheduler cylinder counted by the padded semantic bind is a literal raw
word whose actual length-`16*n^2+2*n` endpoint has rank below `r`. -/
theorem rankBlockBindPaddedMass_le_literalPhiDropMass
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    rankBlockBindPaddedMass hk ring hn3 hndvd C tail hone hrank hr1 <=
      literalPhiDropMass hk ring r C (16 * n ^ 2 + 2 * n) := by
  rw [← localHitCount_eq_literalPhiDropMass
    hn3 hndvd C tail hone (16 * n ^ 2 + 2 * n)]
  exact rankBlockBindPaddedMass_le_literalRankDropHitCount
    hk ring hn3 hndvd C tail hone hrank hr1

theorem literalPhiDropMass_one_over_thirty_two_padded_horizon
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (16 * n ^ 2 + 2 * n) <=
      32 * literalPhiDropMass hk ring r C (16 * n ^ 2 + 2 * n) := by
  exact Nat.le_trans
    (rankBlockBind_success_one_over_thirty_two_padded_horizon
      hk ring hn3 hndvd C tail hone hrank hr1)
    (Nat.mul_le_mul_left 32
      (rankBlockBindPaddedMass_le_literalPhiDropMass
        hk ring hn3 hndvd C tail hone hrank hr1))

end RankBlockBind
end CenteredRenewal
end AAFJPK
