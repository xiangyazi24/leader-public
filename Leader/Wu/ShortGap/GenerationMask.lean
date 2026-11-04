import Leader.Wu.ShortGap.LineageRetained

/-!
# Generation masks, comparison history, and the accounting-cut obstruction

Generation masks are monotone and reproduce the exact history-word step.
DenialOnly is stated using the completed-comparison prefix and immutable
payload history. On Lineage' it is equivalent to requiring a denial witness
for every completed comparison, so missing history is not assumed away.

The requested Bellman domain does not require entry into the predecessor
cohort. The counterexamples below test that omission at a clean uniform
start, already with h=1: future latent tokens cannot be advanced by current
old-cohort interactions. No scheduler edge is discarded or relabelled.
-/
namespace ShortGapGenerationMask
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapDenialTransportLiteral
open ShortGapJoinedIncidenceBalance FiniteUniformStoppingTree
set_option autoImplicit false

def genMask (R : RFrame) (r : Nat) (s : GhostRing R) (i : Fin R.m) : Bool := decide (r ≤ s.k i)

theorem genMask_monotone_step (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (i : Fin R.m) (h : genMask R r s i = true) :
    genMask R r (ghostStep' R s e) i = true := by
  have hr : r ≤ s.k i := by simpa [genMask] using h
  have hk : s.k i ≤ (ghostStep' R s e).k i := Nat.le_add_right _ _
  simp [genMask, Nat.le_trans hr hk]

theorem wordOf'_step (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hs : Lineage' R s) : wordOf R r (ghostStep' R s e) =
      joinedIncidenceStep (placement R) (genMask R r s) (wordOf R r s) (encode R e) :=
  ShortGapLineageRetained.wordOf'_step R r s hs e

def latentDebt (R : RFrame) (r : Nat) (s : GhostRing R) : Nat :=
  litTotalHops (tokensOf' R r s)

/-- Round zero has a virtual completed predecessor. At r=q+1, only pairs
whose round-q comparison has completed are constrained. Uncompared virtual
candidates are allowed; the accounting classifier can stop at them early. -/
def DenialOnly (R : RFrame) : Nat → GhostRing R → Prop
  | 0, _ => True
  | q+1, s => ∀ g c d, ComparedAt ((prefixView R s).epoch g) q →
      s.hist g q = some c → s.hist (next R g) q = some d → res c d = .denial

theorem denialOnly_iff_comparisons (R : RFrame) (q : Nat) (s : GhostRing R)
    (hs : Lineage' R s) : DenialOnly R (q+1) s ↔
      ∀ g, ComparedAt ((prefixView R s).epoch g) q → HistoricalDenial R s g q := by
  constructor
  · intro hd g hg
    obtain ⟨c,d,hc,hd'⟩ := hs.coherent.prefixPayloads g q hg
    exact ⟨c,d,hc,hd',hd g c d hg hc hd'⟩
  · intro hd g c d hg hc hd'
    obtain ⟨c',d',hc',hd'',hv⟩ := hd g hg
    rw [hc] at hc'; rw [hd'] at hd''
    cases hc'; cases hd''; exact hv

private theorem not_denial_candidate (c d : Choice) (h : res c d ≠ .denial) :
    c = .out1 ∧ d = .in0 := by
  cases c <;> cases d <;> simp_all [res]

/-- This dichotomy applies at every state, hence in particular after a
DenialOnly step. Failure of denial-only comparison history exposes an actual
historical out1/in0 pair, rather than a receipt-based success guess. -/
theorem denialOnly_or_virtualSuccess (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (_hd : DenialOnly R r s) :
    DenialOnly R r (ghostStep' R s e) ∨ VirtualCandidate R (r-1) (ghostStep' R s e) := by
  classical
  cases r with
  | zero => exact Or.inl trivial
  | succ q =>
    by_cases hd : DenialOnly R (q+1) (ghostStep' R s e)
    · exact Or.inl hd
    · apply Or.inr
      apply Classical.byContradiction
      intro hv
      apply hd
      intro g c d _ hc hd'
      apply Classical.byContradiction
      intro hn
      obtain ⟨rfl,rfl⟩ := not_denial_candidate c d hn
      apply hv
      refine ⟨g, ?_, ?_⟩
      · simp [wordOf, hc, choiceToWord]
      · simp [wordOf, ring_next, hd', choiceToWord]

theorem denialOnly_start (R : RFrame) (r : Nat) : DenialOnly R r (ghostStart R) := by
  cases r with
  | zero => trivial
  | succ q => intro g c d h; exact False.elim h

theorem uniform_history_denial (R : RFrame) (q : Nat) (s : GhostRing R)
    (b : Choice) (hb : ∀ i, s.hist i q = some b) : DenialOnly R (q+1) s := by
  intro g c d _ hc hd
  rw [hb] at hc; rw [hb] at hd
  cases hc; cases hd
  cases b <;> rfl

/-- Denial-only does not repair the earlier strict Lineage' closure failure.
Both sides of that reachable relaunch still have all-denial round-0 history.
The generation-mask results below are statewise, not a claimed invariant
induction for every reachable prefix. -/
theorem lineage_denialOnly_not_closed :
    Reachable' T launchReady ∧ Lineage' T launchReady ∧ DenialOnly T 1 launchReady ∧
    DenialOnly T 1 (ghostStep' T launchReady (E 1)) ∧
    ¬ Lineage' T (ghostStep' T launchReady (E 1)) := by
  refine ⟨launchReady_reachable,launchReady_lineage,?_,?_,lineage'_step.2.2⟩
  · exact uniform_history_denial T 0 launchReady .out1 (fun _ => rfl)
  · exact uniform_history_denial T 0 _ .out1
      (fun i => hist'_monotone T launchReady (E 1) i 0 .out1 rfl)

/-- A preserved service-entry lower bound. Its omission, rather than the
generation mask, is what the future-cohort Bellman counterexample detects. -/
def CohortEntered (R : RFrame) : Nat → GhostRing R → Prop
  | 0, _ => True
  | q+1, s => ∀ i, q ≤ s.k i

theorem cohortEntered_step (R : RFrame) (r : Nat) (s : GhostRing R) (e : Vtx R)
    (hs : CohortEntered R r s) : CohortEntered R r (ghostStep' R s e) := by
  cases r with
  | zero => trivial
  | succ q => intro i; exact Nat.le_trans (hs i) (Nat.le_add_right _ _)

/-- The balance theorem's usual round-domain assumption is explicit. This
uses the generation mask directly, with no receipt-mask reconstruction. -/
theorem genMask_abstract_localBalance (R : RFrame) (r : Nat) (s : GhostRing R)
    (b : PeriodHIncidenceChoice.FrozenValue)
    (hb : PeriodHIncidenceChoice.BaseOrRace b (wordOf R r s))
    (hr : PeriodHIncidenceChoice.HasRace (wordOf R r s)) :
    joinedBadEdgeCount b (placement R) (genMask R r s) (wordOf R r s) ≤
      joinedGoodEdgeCount (ring R) (placement R) (genMask R r s) (wordOf R r s) := by
  have hm : 1 < R.m := by have := R.hm; omega
  have hn : 1 < R.n := by
    have hh := R.hh
    have hx : R.m ≤ R.m * R.h := by simpa using Nat.mul_le_mul_left R.m hh
    change 1 < R.m * R.h
    omega
  exact joinedGoodEdgeCount_ge_joinedBadEdgeCount (ring R) hm (placement R) hn b _ _ hb hr

theorem encode_edgeVtx (R : RFrame) (e : Fin R.n) : encode R (edgeVtx R e) = e := by
  apply Fin.ext
  change R.h * (e.val / R.h) + e.val % R.h = e.val
  simpa only [Nat.add_comm] using Nat.mod_add_div e.val R.h

noncomputable def genGoodEdgeCount (R : RFrame) (r : Nat) (s : GhostRing R) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if VirtualCandidate R r (ghostStep' R s (edgeVtx R e)) then 1 else 0)).sum

noncomputable def genBadEdgeCount (R : RFrame) (r : Nat) (s : GhostRing R)
    (b : PeriodHIncidenceChoice.FrozenValue) : Nat := by
  classical
  exact (List.ofFn (fun e : Fin R.n =>
    if ∀ i, wordOf R r (ghostStep' R s (edgeVtx R e)) i = b.toChoice then 1 else 0)).sum

theorem genGoodEdgeCount_eq (R : RFrame) (r : Nat) (s : GhostRing R) (hs : Lineage' R s) :
    genGoodEdgeCount R r s = joinedGoodEdgeCount (ring R) (placement R) (genMask R r s) (wordOf R r s) := by
  classical
  unfold genGoodEdgeCount joinedGoodEdgeCount joinedGoodEdge JoinedCreatesCandidate VirtualCandidate
  apply ofFn_sum_eq
  intro e
  rw [wordOf'_step R r s _ hs,encode_edgeVtx]
  simp

theorem genBadEdgeCount_eq (R : RFrame) (r : Nat) (s : GhostRing R) (hs : Lineage' R s)
    (b : PeriodHIncidenceChoice.FrozenValue) :
    genBadEdgeCount R r s b = joinedBadEdgeCount b (placement R) (genMask R r s) (wordOf R r s) := by
  classical
  unfold genBadEdgeCount joinedBadEdgeCount joinedBadEdge JoinedRestoresBase
  apply ofFn_sum_eq
  intro e
  rw [wordOf'_step R r s _ hs,encode_edgeVtx]
  simp

/-- Balance for actual ghostStep' scheduler children, not merely abstract
edge counts. The BaseOrRace premise of the inherited round theorem is kept. -/
theorem genPipelined_localBalance (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage' R s) (b : PeriodHIncidenceChoice.FrozenValue)
    (hb : PeriodHIncidenceChoice.BaseOrRace b (wordOf R r s))
    (hr : PeriodHIncidenceChoice.HasRace (wordOf R r s)) :
    genBadEdgeCount R r s b ≤ genGoodEdgeCount R r s := by
  rw [genBadEdgeCount_eq R r s hs b,genGoodEdgeCount_eq R r s hs]
  exact genMask_abstract_localBalance R r s b hb hr

/-- A complete conditional monotonicity consumer of the proposed transport
simulation. The extra hypothesis is explicit; it is not supplied by Lineage'. -/
theorem latentDebt_step_le_of_simulation (R : RFrame) (r : Nat) (s : GhostRing R)
    (e : Vtx R) (hs : TokenSimulation R r s e) :
    latentDebt R r (ghostStep' R s e) ≤ latentDebt R r s := by
  rcases hs with h | h
  · unfold latentDebt
    rw [h]
    exact litTotalHops_multiLitLocalStep_le _ _ _
  · unfold latentDebt
    rw [h]
    exact Nat.le_refl _

/-- The bounded scan recovers the unique live slot for arbitrary gap length.
This proves scan correctness without a small-h restriction or a recursion
limit override. It does not assume a phase-step simulation equation. -/
theorem tokenPos_of_unique (R : RFrame) (s : GhostRing R) (g : Fin R.m)
    (p : Fin R.h) (hp : 0 < p.val) (t : Slot) (ht : t ≠ .empty)
    (hs : ∀ a : Fin R.h, 0 < a.val →
      s.cfg (g,a) = .interior (if a = p then t else .empty)) : tokenPos R s g = p.val := by
  let P : Fin R.h → Bool := fun a => decide (0 < a.val) &&
    match s.cfg (g,a) with
    | .interior (.decl _) | .interior (.reply _) => true
    | _ => false
  have hpp : P p = true := by
    have hh := hs p hp
    cases t with
    | empty => exact False.elim (ht rfl)
    | decl c => simp [P,hh,hp]
    | reply d => simp [P,hh,hp]
  have unique : ∀ a, P a = true → a = p := by
    intro a ha
    have ha0 : 0 < a.val := by
      by_cases hh : 0 < a.val
      · exact hh
      · simp [P,hh] at ha
    by_cases h : a = p
    · exact h
    · have hh := hs a ha0
      simp [P,hh,h] at ha
  have hfind : (List.finRange R.h).find? P = some p := by
    cases he : (List.finRange R.h).find? P with
    | none =>
      have hn := (List.find?_eq_none.mp he) p (List.mem_finRange p)
      exact False.elim (hn hpp)
    | some a =>
      have ha := unique a (List.find?_some he)
      subst a; rfl
  change (((List.finRange R.h).find? P).map Fin.val).getD 0 = p.val
  rw [hfind]
  rfl

theorem tokenPos_bounds (R : RFrame) (s : GhostRing R) (g : Fin R.m)
    (t : Slot) (ht : t ≠ .empty) (hs : OneToken R s g t) :
    0 < tokenPos R s g ∧ tokenPos R s g < R.h := by
  obtain ⟨p,hp,hslots⟩ := hs
  rw [tokenPos_of_unique R s g p hp t ht hslots]
  exact ⟨hp,p.isLt⟩

private theorem latent_hops_pos (R : RFrame) : 0 < (LitGapState.declareAt 0 R.hh).hops := by
  change 0 < 2 * R.h - 1 - 0
  have := R.hh
  omega

/-- Zero debt in one gap implies its predecessor delivery prefix is complete.
The live cases use the arbitrary-h scan theorem above, so malformed fallback
positions cannot fabricate zero debt in a Lineage' state. -/
theorem zero_token_completed (R : RFrame) (q : Nat) (s : GhostRing R)
    (hs : Lineage' R s) (g : Fin R.m) (hz : (tokensOf' R (q+1) s g).hops = 0) :
    DeliveredAt ((prefixView R s).epoch g) q := by
  by_cases hpast : q < s.k g
  · exact (hs.coherent.joinedDenials g q hpast).1
  · by_cases hfuture : s.k g < q
    · have hh := latent_hops_pos R
      simp only [tokensOf',cohortToken,if_neg hpast,if_pos hfuture] at hz
      omega
    · have hk : s.k g = q := by omega
      simp only [tokensOf',cohortToken,if_neg hpast,if_neg hfuture] at hz
      cases he : s.epoch g with
      | idle =>
        simp only [he] at hz
        have hh := latent_hops_pos R; omega
      | outbound t c =>
        simp only [he] at hz
        by_cases hq : t = q
        · rw [if_pos hq] at hz
          have hshape := hs.coherent.shape g
          simp only [EpochShape,prefixView,he] at hshape
          have hb := tokenPos_bounds R s g (.decl c) (by intro h; cases h) hshape.2.2.2
          have hh := R.hh
          simp [ofPhase,hb.2,LitGapState.hops] at hz
          omega
        · rw [if_neg hq] at hz
          have hh := latent_hops_pos R; omega
      | returning t c d =>
        simp only [he] at hz
        by_cases hq : t = q
        · rw [if_pos hq] at hz
          have hshape := hs.coherent.shape g
          simp only [EpochShape,prefixView,he] at hshape
          have hb := tokenPos_bounds R s g (.reply d) (by intro h; cases h) hshape.2.2.2.2
          have hle : tokenPos R s g ≤ R.h - 1 := by omega
          have hge : 1 ≤ tokenPos R s g := by omega
          simp [ofPhase,hge,hle,LitGapState.hops] at hz
          omega
        · rw [if_neg hq] at hz
          have hh := latent_hops_pos R; omega
      | delivered t c d =>
        simp only [he] at hz
        by_cases hq : t = q
        · simp [prefixView,he,DeliveredAt,hq]
        · rw [if_neg hq] at hz
          have hh := latent_hops_pos R; omega

private theorem sum_zero_point {m : Nat} (f : Fin m → Nat)
    (h : (List.ofFn f).sum = 0) : ∀ i, f i = 0 := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons] at h
    intro i
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i; omega
    · have hip : 0 < i.val := by omega
      let j : Fin m := ⟨i.val-1,by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have hz := ih (fun a => f a.succ) (by omega) j
      simpa only [hj] using hz

private theorem view_k (R : RFrame) (s : GhostRing R) : (prefixView R s).k = s.k := rfl
private theorem view_hist (R : RFrame) (s : GhostRing R) : (prefixView R s).hist = s.hist := rfl
private theorem view_cfg (R : RFrame) (s : GhostRing R) : (prefixView R s).cfg = s.cfg := rfl

/-- The required bridge is positive on the stated denial-only domain. Race
is unnecessary: any unjoined owner forces remaining predecessor debt. -/
theorem unjoined_gen_has_debt (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage' R s) (hd : DenialOnly R r s)
    (i : Fin R.m) (hi : s.k i < r) : 0 < latentDebt R r s := by
  apply Nat.pos_of_ne_zero
  intro hz
  cases r with
  | zero => omega
  | succ q =>
    have allzero := sum_zero_point (fun g => (tokensOf' R (q+1) s g).hops) hz
    have ho := zero_token_completed R q s hs i (allzero i)
    have hp := zero_token_completed R q s hs (prev R i) (allzero (prev R i))
    have hq : s.k i = q := by
      have hh := hs.coherent.shape i
      cases he : (prefixView R s).epoch i <;> simp only [EpochShape,he,view_k] at hh
      all_goals simp only [he,DeliveredAt] at ho
      all_goals change s.k i < q+1 at hi
      all_goals omega
    have hc0 := hs.coherent.outgoingValue i (by simpa only [view_k,hq] using ho)
    obtain ⟨c,d,hc,hd',hw⟩ := hc0
    have hcomp : ComparedAt ((prefixView R s).epoch i) q := by
      cases he : (prefixView R s).epoch i <;> simp_all only [DeliveredAt,ComparedAt]
      all_goals omega
    have hv := hd i c d hcomp (by simpa only [view_hist,view_k,hq] using hc)
      (by simpa only [view_hist,view_k,hq] using hd')
    have hcw : (s.cfg (rootV R i)).cwPort = some .heldDenial := by
      change (s.cfg (rootV R i)).cwPort = some (resCw c d) at hw
      simpa only [resCw,hv,Verdict.cw] using hw
    have hcompPrev : ComparedAt ((prefixView R s).epoch (prev R i)) q := by
      cases he : (prefixView R s).epoch (prev R i) <;> simp_all only [DeliveredAt,ComparedAt]
      all_goals omega
    have hvp := hs.coherent.incomingValue (prev R i)
      (by simpa only [view_k,next_prev,hq] using hcompPrev)
    obtain ⟨c',d',hc',hd'',hw'⟩ := hvp
    have hv' := hd (prev R i) c' d' hcompPrev
      (by simpa only [view_hist,view_k,next_prev,hq] using hc')
      (by simpa only [view_hist,view_k,next_prev,hq] using hd'')
    have hccw : (s.cfg (rootV R i)).ccwPort = some .heldDenial := by
      simpa only [view_cfg,next_prev,resCcw,hv',Verdict.ccw] using hw'
    obtain ⟨ch,cw,ccw,hroot⟩ := hs.coherent.roots i
    change s.cfg (rootV R i) = .root ch cw ccw at hroot
    rw [hroot] at hcw hccw
    have hcw' : cw = .heldDenial := Option.some.inj hcw
    have hccw' : ccw = .heldDenial := Option.some.inj hccw
    have hn := hs.coherent.normalized i
    change joinReady (s.cfg (rootV R i)) = false at hn
    rw [hroot,hcw',hccw'] at hn
    cases hn

/-- Zero predecessor debt on the denial-only domain implies the actual
generation cut. No receipt-based mask equivalence is used. -/
theorem latentDebt_zero_all_joined (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage' R s) (hd : DenialOnly R r s) (hz : latentDebt R r s = 0) :
    ∀ i, r ≤ s.k i := by
  intro i
  have hn : ¬ s.k i < r := by
    intro hi
    have hh := unjoined_gen_has_debt R r s hs hd i hi
    omega
  omega

theorem latentDebt_zero_step (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage' R s) (hd : DenialOnly R r s) (hz : latentDebt R r s = 0) (e : Vtx R) :
    latentDebt R r (ghostStep' R s e) = 0 := by
  have hj := latentDebt_zero_all_joined R r s hs hd hz
  have hj' : ∀ i, r ≤ (ghostStep' R s e).k i := fun i => Nat.le_trans (hj i) (Nat.le_add_right _ _)
  have ht := all_joined_tokens_done R r (ghostStep' R s e) hj'
  simp [latentDebt,litTotalHops,ht,LitGapState.hops,ofFn_sum_const]

private theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · have he : i = 0 := Fin.ext h; exact he ▸ h0
  · have he : i = 1 := Fin.ext h; exact he ▸ h1
  · have he : i = 2 := Fin.ext h; exact he ▸ h2

private theorem forall_one {P : Fin 1 → Prop} (h0 : P 0) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  have he : i = 0 := Fin.ext (by change i.val = 0; omega)
  exact he ▸ h0

abbrev D : RFrame := DirectFrame
abbrev cold : GhostRing D := ghostStart D

theorem cold_future_debt : latentDebt D 2 cold = 3 := by decide

theorem cold_every_edge_stalls : ∀ e : Vtx D,
    latentDebt D 2 (ghostStep' D cold e) = 3 ∧
    PeriodHIncidenceChoice.choiceRaceReserve (wordOf D 2 (ghostStep' D cold e)) = 3 := by
  intro ⟨g,a⟩
  revert g a; apply forall_three <;> apply forall_one <;> decide

/-- No advancing physical edge exists at all in this positive-debt example;
choosing a different live/latent token cannot rescue the requested progress. -/
theorem cold_no_useful_edge : ¬ ∃ e : Vtx D,
    latentDebt D 2 (ghostStep' D cold e) < latentDebt D 2 cold := by
  rintro ⟨e,he⟩
  rw [(cold_every_edge_stalls e).1,cold_future_debt] at he
  omega

/-- COUNTEREXAMPLE to useful-edge progress, even with h=1, Lineage',
DenialOnly and an unjoined Race root. No owner has entered predecessor round 1. -/
theorem advancing_edge_lowers_latentDebt :
    Reachable' D cold ∧ Lineage' D cold ∧ DenialOnly D 2 cold ∧
    (tokensOf' D 2 cold 0).advanceEdge = some (0 : Fin 1) ∧
    0 < latentDebt D 2 cold ∧
    ¬ latentDebt D 2 (ghostStep' D cold (directEdge 0)) < latentDebt D 2 cold := by
  exact ⟨⟨[],rfl⟩,lineage'_start D,denialOnly_start D 2,rfl,by decide,by decide⟩

def roundDebt (R : RFrame) (r : Nat) (s : GhostRing R) : Nat :=
  PeriodHIncidenceChoice.choiceRaceReserve (wordOf R r s) + latentDebt R r s

/-- The joined-Race branch of the requested accounting is established once
carrier nonincrease is supplied. The debt premise is not hidden in Lineage'. -/
theorem genPipelined_childSum_of_joined (R : RFrame) (r : Nat) (s : GhostRing R)
    (hs : Lineage' R s)
    (hj : ∃ i, wordOf R r s i = .race ∧ genMask R r s i = true)
    (hd : ∀ e, latentDebt R r (ghostStep' R s e) ≤ latentDebt R r s) :
    1 + (List.ofFn (fun e : Fin R.n => roundDebt R r (ghostStep' R s (edgeVtx R e)))).sum ≤
      R.n * roundDebt R r s := by
  have hword := joinedReserve_childSum (placement R) (genMask R r s) (wordOf R r s) hj
  have hsum : (List.ofFn (fun e : Fin R.n =>
      PeriodHIncidenceChoice.choiceRaceReserve (wordOf R r (ghostStep' R s (edgeVtx R e))))).sum =
      (List.ofFn (fun e : Fin R.n => PeriodHIncidenceChoice.choiceRaceReserve
        (joinedIncidenceStep (placement R) (genMask R r s) (wordOf R r s) e))).sum := by
    apply ofFn_sum_eq
    intro e
    rw [wordOf'_step R r s _ hs,encode_edgeVtx]
  have hdebt := ofFn_sum_le
    (fun e : Fin R.n => latentDebt R r (ghostStep' R s (edgeVtx R e)))
    (fun _ => latentDebt R r s) (fun e => hd (edgeVtx R e))
  rw [ofFn_sum_const] at hdebt
  unfold roundDebt
  rw [ofFn_sum_add,hsum,Nat.mul_add]
  omega

/-- COUNTEREXAMPLE to the requested child sum: each of the three actual
children has reserve+debt=6, so the asserted inequality would be 19 <= 18.
The same domain omission already defeats the h<=2 fallback. -/
theorem genPipelined_childSum :
    Reachable' D cold ∧ Lineage' D cold ∧ DenialOnly D 2 cold ∧
    PeriodHIncidenceChoice.HasRace (wordOf D 2 cold) ∧
    ¬ (1 + (List.ofFn (fun e : Fin D.n =>
        roundDebt D 2 (ghostStep' D cold (edgeVtx D e)))).sum ≤ D.n * roundDebt D 2 cold) := by
  refine ⟨⟨[],rfl⟩,lineage'_start D,denialOnly_start D 2,⟨0,rfl⟩,?_⟩
  decide

theorem missing_cohort_entry : ¬ CohortEntered D 2 cold := by
  intro h; have hh := h 0; change 1 ≤ 0 at hh; omega

/-!
Stall boundary. The requested useful-edge and child-sum statements are false
on their given Lineage' + DenialOnly domain, already for h=1. The preserved
CohortEntered lower bound excludes this counterexample; it is not silently
added to either negative theorem. A repaired service progress theorem must
use that cut and establish actual movement of a tracked current token.

The arbitrary-h scan itself is now proved (tokenPos_of_unique and bounds),
and it discharges unjoined_gen_has_debt on the denial-only domain. General
positive-debt step nonincrease remains OPEN: latentDebt_step_le_of_simulation
is explicitly conditional on TokenSimulation, and latentDebt_zero_step is
unconditional only on the zero-debt slice with its stated invariant/domain.
No theorem named latentDebt_step_le is presented as a general row result.
The two counterexamples prevent completing the requested h<=2 Bellman case
as stated. No composed stopping-tree budget or physical latch bound is claimed.
DenialOnly also leaves the inherited strict Lineage' closure counterexample
intact (lineage_denialOnly_not_closed); a complete run theorem must repair
that predicate in addition to supplying the service-entry cut.
-/

#print axioms genMask_monotone_step
#print axioms wordOf'_step
#print axioms tokenPos_of_unique
#print axioms unjoined_gen_has_debt
#print axioms denialOnly_or_virtualSuccess
#print axioms lineage_denialOnly_not_closed
#print axioms latentDebt_step_le_of_simulation
#print axioms latentDebt_zero_step
#print axioms advancing_edge_lowers_latentDebt
#print axioms genPipelined_childSum
#print axioms genPipelined_childSum_of_joined
#print axioms genPipelined_localBalance

end ShortGapGenerationMask
