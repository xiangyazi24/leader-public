import Leader.L4.Height.ServiceCustody
import Leader.L4.BStarPostCutOperands
import Leader.L4.BStarNeedTailService
import Leader.Wu.Scheduler.OrderedWordScheduler
import Leader.Wu.Scheduler.UniformFirstHitExpectation
import Leader.L4.Height.G9Core

namespace L4.Height.RawServiceCore
open AllSizeProtocol BStarLongWork BStarH6WordChart BStarAcquireLiteralChain
open BStarGrantWriterHistory BStarGrantBirth BStarCommitOperands BStarLongGrant
open L4.PhysicalCustody
open Classical

noncomputable section

/-- Full Cartesian initial state for the one-header counterexample. The
lower sets have spacings 3, 9, 27 and 81. The two singleton report
layers have zero selected thresholds and an initially positive pulse. -/
def singletonSeed : Raw 6 81 := fun j =>
  let k := j.val
  let flag (p : Bool) (b : Nat) := p.toNat * 2 ^ b
  let mis (spacing : Nat) : BitVec 96 := BitVec.ofNat 96
    (min 3 (k % spacing) * 2^94 + flag ((k+1) % spacing == 0) 93 +
      (if k % (3*spacing) == 0 then 2^88 + 2^87 else 0))
  let report (p : ReportByteRows.Params) : BitVec p.w :=
    BitVec.ofNat p.w (min (max 3 p.digits) k * 2^(ReportByteRows.workW p + 1) +
      flag (k == 80) (ReportByteRows.workW p) + flag (k == 0) (ell p.streak + 2))
  { physical := BitVec.ofNat 6 (flag (k%3 == 0) 2 + flag (k%3 == 1) 1 + flag (k%3 == 2) 0)
    mis1 := mis 3, mis2 := mis 9, mis3 := mis 27
    report1 := report ⟨7, 1, 6, streak 6⟩
    report2 := report ⟨2, ell (radiusTwo 6 + 1), radiusTwo 6, streak (radiusTwo 6)⟩
    widthClient := BitVec.ofNat _ (min 17 k * 2^30 + flag (k == 80) 29 +
      flag (k < 63) 26 + flag (k == 62) 25 + flag (k == 0) 21)
    long := BitVec.ofNat _ (min 5 k * 2^2364 + flag (k == 80) 2363 +
      flag (k == 61) 2362 + flag (k == 0) 2204)
    guard := 0, publicRow := 0 }

private theorem different_endpoints {n : Nat} (hn : 4 ≤ n) (e : Fin n) :
    e ≠ rightNeighbor e := by
  intro eq
  have h := congrArg Fin.val eq
  change e.val = (e.val + 1) % n at h
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have last : e.val + 1 = n := by omega
    rw [last, Nat.mod_self] at h
    omega

private theorem live_at_end {s n : Nat} {x : Raw s n}
    {cut tape : List (Fin n)} {i : Fin n} {j : Fin 3}
    (a : Acquisition (show 0 < 2 by decide) x cut tape i j) :
    bit (rawRun x tape) i j ≠ 0 := by
  have h := a.live a.post [] (List.append_nil _).symm
  have eq : rawRun x tape = rawRun (rawNext s (rawRun x a.lead) a.mark) a.post := by
    exact (congrArg (rawRun x) a.exactTape).trans
      (BStarResetSchedule.run_append (rawNext s) x a.lead (a.mark :: a.post))
  rw [eq]
  exact h

/-- A physical COMMIT needs distinct reader and writer sites, because
The production run extracts both live acquisitions on the same old tape. -/
theorem different_headers_of_publication {s n : Nat} (hn : 4 ≤ n)
    {x : Raw s n} (g : CustodyWitness x) (i : Fin n) (w : List (Fin n))
    (pub : publishes x i w) :
    ∃ a b : BStarAcquireAnchors.Header (oldH6 (rows s) g.base), a.val ≠ b.val := by
  obtain ⟨pre, _, _, mark⟩ := pub
  let tape := g.u ++ (g.v ++ (g.past ++ pre))
  have whole : rawRun g.initial tape = rawRun x pre := by
    calc
      rawRun g.initial tape =
          rawRun g.initial (((g.u ++ g.v) ++ g.past) ++ pre) := by
            simp only [tape, List.append_assoc]
      _ = rawRun (rawRun g.initial ((g.u ++ g.v) ++ g.past)) pre :=
        BStarResetSchedule.run_append (rawNext s) _ _ _
      _ = rawRun x pre := by rw [g.here]
  have hmark : ¬ NoPublication (show 0 < 2 by decide)
      (rawRun g.initial ((g.u ++ g.v) ++ (g.past ++ pre))) i i := by
    rw [List.append_assoc]
    change ¬ NoPublication (show 0 < 2 by decide) (rawRun g.initial tape) i i
    rw [whole]
    exact mark
  obtain ⟨o, _, _, _, allPorts⟩ := BStarPostCutOperands.actual_operands
    (show 0 < 2 by decide) g.u g.v (g.past ++ pre) g.cuts g.hh
    (different_endpoints hn) g.Q g.init g.fiber g.closed i i hmark
  obtain ⟨a, _, acqA, _, siteA, _⟩ := allPorts 0
  obtain ⟨b, _, acqB, _, siteB, _⟩ := allPorts 1
  have headA : oldH6 (rows s) g.base a = true := by
    rw [siteA]
    exact (endpoint_spec _ g.hh o 0).1
  have headB : oldH6 (rows s) g.base b = true := by
    rw [siteB]
    exact (endpoint_spec _ g.hh o 1).1
  refine ⟨⟨a, headA⟩, ⟨b, headB⟩, ?_⟩
  intro same
  change a = b at same
  have qrun (z : Raw s n) (u : List (Fin n)) (h : g.Q z) : g.Q (rawRun z u) := by
    induction u generalizing z with
    | nil => exact h
    | cons e u ih => exact ih _ (g.closed _ e h)
  let z := rawRun g.initial tape
  have clean := g.coherent z (qrun _ tape g.init) b
  have reader : bit z b 0 ≠ 0 := same ▸ live_at_end acqA
  have writer : bit z b 1 ≠ 0 := live_at_end acqB
  have r := BStarGrantReaderHistory.canonical_of_live z b 0 clean reader
  have t := BStarGrantReaderHistory.canonical_of_live z b 1 clean writer
  rw [BStarLongGrantProjection.canonical_clean _ clean] at r t
  simp [conflict, r, t] at clean

/-- The strict numerator vanishes at every horizon on a singleton fibre. -/
theorem singleton_publication_mass {s n : Nat} (hn : 4 ≤ n)
    {x : Raw s n} (g : CustodyWitness x)
    (only : ∀ a b : BStarAcquireAnchors.Header (oldH6 (rows s) g.base), a.val = b.val)
    (i : Fin n) (t : Nat) :
    L4.Height.wordSum (fun w => if publishes x i w then 1 else 0) t = 0 := by
  have never (w : List (Fin n)) : ¬ publishes x i w := by
    intro event
    obtain ⟨a, b, ne⟩ := different_headers_of_publication hn g i w event
    exact ne (only a b)
  simp only [if_neg (never _)]
  exact L4.Height.wordSum_zero t

/-- This includes the exact multiplier and horizon of the proposed export. -/
theorem singleton_refutes_block {s n : Nat} (hn : 4 ≤ n) {x : Raw s n}
    (g : CustodyWitness x)
    (only : ∀ a b : BStarAcquireAnchors.Header (oldH6 (rows s) g.base), a.val = b.val)
    (i : BStarAcquireAnchors.Header (oldH6 (rows s) g.base)) (weight horizon : Nat) :
    weight * L4.Height.wordSum (fun w => if publishes x i.val w then 1 else 0) horizon
      < n ^ horizon := by
  rw [singleton_publication_mass hn g only i.val horizon, Nat.mul_zero]
  exact Nat.pow_pos (by omega)

/-- On a repaired chart the positive-prefix block count yields the service
moment on the original history-bearing clock chain. -/
theorem service_moment_of_prefix_count {α : Type} {n m B M H d L : Nat}
    {hm : 0 < m} (C : Recover.Chain.ClockChain α n m B M hm) (i : Fin m)
    (hH : 1 ≤ H) (hd : 1 ≤ d) (hL : 4 * (d * H) ≤ L)
    (mass : ∀ z, n ^ H ≤ d * Thru.wordSum
      (fun w => if RawService.hasPublication C.next (C.served i) z w then 1 else 0) H) :
    ∀ z, Thru.MomentAt C.next (C.served i) L z := by
  apply RawService.publication_moment_of_block _ _ H d L hH hd hL
  simpa only [RawService.publicationMass_eq_prefix] using mass

/-- Censored time to the next actual center publication, counting its mark. -/
def strictWait {s n : Nat} (x : Raw s n) (i : Fin n) : List (Fin n) → Nat
  | [] => 0
  | e :: w =>
    if e = i ∧ ¬ NoPublication (show 0 < 2 by decide) x i i then 1
    else 1 + strictWait (rawNext s x e) i w

/-- A vacant center slot, for example on a clean reset, admits no
one-mark strict publication on any label. -/
theorem empty_center_misses {s n : Nat} (x : Raw s n) (i e : Fin n)
    (empty : BStarLongToken.atSite (x i).long 1 = .empty) :
    ¬ publishes x i [e] := by
  intro event
  rcases (publishes_cons x i e []).mp event with ⟨_, yes⟩ | rest
  · apply yes
    intro side loc a member
    obtain ⟨_, q, front, _⟩ := (BStarLongLiteral.raw_literal_commit_iff _ _ a).mp member
    change BStarLongCommand.bind (longGeometry (rows s) (x i)) 1 (BStarLongToken.atSite (x i).long 1) = .forward q at front
    rw [empty] at front
    cases front
  · exact publishes_nil _ _ rest

private theorem strictWait_of_miss {s n : Nat} (x : Raw s n) (i : Fin n)
    (w : List (Fin n)) (miss : ¬ publishes x i w) : strictWait x i w = w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have first := fun h => miss ((publishes_cons x i e w).2 (Or.inl h))
    have tail := fun h => miss ((publishes_cons x i e w).2 (Or.inr h))
    rw [strictWait, if_neg first, ih _ tail, List.length_cons, Nat.one_add]

/-- At two scales, the singleton's normalized strict moment is exactly four. -/
theorem singleton_strict_moment {s n : Nat} (hn : 4 ≤ n) {x : Raw s n}
    (g : CustodyWitness x)
    (only : ∀ a b : BStarAcquireAnchors.Header (oldH6 (rows s) g.base), a.val = b.val)
    (i : Fin n) (L : Nat) (pos : 0 < L) :
    L4.Height.wordSum (fun w => 2 ^ (min (strictWait x i w) (2 * L) / L)) (2 * L) =
      4 * n ^ (2 * L) := by
  rw [L4.Height.repair_wordSum_eq_thru]
  calc
    _ = Thru.wordSum (fun _ : Thru.Word n => 4) (2 * L) := by
      apply Thru.wordSum_congr_length
      intro w len
      have miss : ¬ publishes x i w := by
        intro p
        obtain ⟨a, b, diff⟩ := different_headers_of_publication hn g i w p
        exact diff (only a b)
      have div : (2 * L) / L = 2 := by
        rw [Nat.mul_comm 2 L, Nat.mul_div_cancel_left _ pos]
      rw [strictWait_of_miss _ _ _ miss, len, Nat.min_self, div]
    _ = _ := Thru.wordSum_const 4 _

/-- Any dyadic service moment already forces at least half of the raw words
to publish by time twice its scale. Together with block renewal this makes
the stopped block condition necessary and sufficient up to constants. -/
theorem block_of_strict_moment {s n : Nat} (x : Raw s n) (i : Fin n) (L : Nat)
    (pos : 0 < L)
    (moment : ∀ t, L4.Height.wordSum
      (fun w => 2 ^ (min (strictWait x i w) t / L)) t ≤ 2 * n ^ t) :
    n ^ (2 * L) ≤ 2 * Thru.wordSum
      (fun w => if publishes x i w then 1 else 0) (2 * L) := by
  let H := 2 * L
  let hit (w : List (Fin n)) : Nat := if publishes x i w then 1 else 0
  let miss (w : List (Fin n)) : Nat := if publishes x i w then 0 else 1
  have parts : Thru.wordSum hit H + Thru.wordSum miss H = n ^ H := by
    rw [← Thru.wordSum_add_fun]
    calc
      _ = Thru.wordSum (fun _ : Thru.Word n => 1) H := by
        apply Thru.wordSum_congr
        intro w
        by_cases p : publishes x i w <;> simp [hit, miss, p]
      _ = _ := Thru.wordSum_const_one H
  have four : 4 * Thru.wordSum miss H ≤ 2 * n ^ H := by
    have bound := moment H
    rw [L4.Height.repair_wordSum_eq_thru] at bound
    refine Nat.le_trans ?_ bound
    rw [← Thru.wordSum_mul_left]
    rw [← L4.Height.repair_wordSum_eq_thru, ← L4.Height.repair_wordSum_eq_thru]
    apply L4.Height.repair_wordSum_mono_length
    intro w len
    by_cases p : publishes x i w
    · simp [miss, p]
    · have div : H / L = 2 := by
        change (2 * L) / L = 2
        rw [Nat.mul_comm 2 L, Nat.mul_div_cancel_left _ pos]
      simp [miss, p, strictWait_of_miss x i w p, len, div]
  change n ^ H ≤ 2 * Thru.wordSum hit H
  omega

private def appendMark {n : Nat} (v : List (Fin n)) (e : Fin n) := v ++ [e]

private theorem run_history {n : Nat} (v w : List (Fin n)) :
    Thru.runWord appendMark v w = v ++ w := by
  induction w generalizing v with
  | nil => simp [Thru.runWord]
  | cons e w ih => simp [Thru.runWord, ih, appendMark, List.append_assoc]

private theorem strictWait_history {s n : Nat} (x : Raw s n) (i : Fin n)
    (v w : List (Fin n)) (miss : ¬ publishes x i v) :
    strictWait (rawRun x v) i w = Thru.wait appendMark (publishes x i) v w := by
  induction w generalizing v with
  | nil => rfl
  | cons e w ih =>
    rw [Thru.wait_cons_of_not _ _ _ miss]
    change strictWait (rawRun x v) i (e :: w) =
      Nat.succ (Thru.wait appendMark (publishes x i) (v ++ [e]) w)
    by_cases now : e = i ∧ ¬ NoPublication (show 0 < 2 by decide) (rawRun x v) i i
    · have hit := (publishes_append_one x i e v).2 (Or.inr now)
      rw [strictWait, if_pos now, Thru.wait_of_hit _ _ _ hit]
    · have still : ¬ publishes x i (v ++ [e]) := by
        rw [publishes_append_one]
        exact fun h => h.elim miss now
      have stepEq : rawRun x (v ++ [e]) = rawNext s (rawRun x v) e :=
        BStarResetSchedule.run_append (rawNext s) x v [e]
      rw [strictWait, if_neg now, ← ih _ still, stepEq, Nat.one_add]

/-- A uniform positive fraction of successful raw continuations suffices
on the actual history tree. Below an already served prefix all continuations
satisfy the predicate. Thus only surviving prefixes incur a proof obligation. -/
theorem strict_moment_of_history_blocks {s n : Nat} (x : Raw s n) (i : Fin n)
    (H d L : Nat) (hH : 1 ≤ H) (hd : 1 ≤ d) (hL : 4 * (d * H) ≤ L)
    (mass : ∀ v : List (Fin n), n ^ H ≤ d * Thru.wordSum
      (fun w => if publishes x i (v ++ w) then 1 else 0) H) (t : Nat) :
    L4.Height.wordSum (fun w => 2 ^ (min (strictWait x i w) t / L)) t ≤ 2 * n ^ t := by
  have blocks (v : List (Fin n)) :
      n ^ H ≤ d * RawService.publicationMass appendMark (publishes x i) v H := by
    rw [RawService.publicationMass_eq_prefix]
    apply Nat.le_trans (mass v) (Nat.mul_le_mul_left d ?_)
    rw [← L4.Height.repair_wordSum_eq_thru, ← L4.Height.repair_wordSum_eq_thru]
    apply L4.Height.repair_wordSum_mono_length
    intro w len
    by_cases yes : publishes x i (v ++ w)
    · have hit : RawService.hasPublication appendMark (publishes x i) v w := by
        refine ⟨w.length, by omega, Nat.le_refl _, ?_⟩
        simpa only [List.take_length, run_history] using yes
      simp [yes, hit]
    · simp [yes]
  have mom := RawService.publication_moment_of_block appendMark (publishes x i)
    H d L hH hd hL blocks [] t
  rw [L4.Height.repair_wordSum_eq_thru]
  have eq (w : List (Fin n)) :
      strictWait x i w = Thru.wait appendMark (publishes x i) [] w :=
    strictWait_history x i [] w (publishes_nil x i)
  simp only [eq]
  exact mom

private theorem schedule_sum {n : Nat} (f : List (Fin n) → Nat) (t : Nat) :
    ((allSchedules n t).map f).sum = Thru.wordSum f t := by
  rw [UniformFirstHit.allSchedules_sum_eq_wordSum]
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    rw [FixedSpanRenewalPayload.wordSum_succ]
    exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e => ih (fun v => f (e :: v)))

private theorem miss_indicator {n : Nat} (labels : List (Fin n)) (t : Nat) :
    PPLLOrderedWordScheduler.orderedWordMissCount labels t =
      Thru.wordSum (fun w => if labels.Sublist w then 0 else 1) t := by
  rw [← schedule_sum]
  unfold PPLLOrderedWordScheduler.orderedWordMissCount
  induction allSchedules n t with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
    by_cases h : labels.Sublist a <;> simp [h, Nat.add_comm]

/-- If one fixed subsequence forces strict service despite all interleavings,
its length controls the raw waiting moment at the initial cut. The proof
restarts a matcher on the same history even across an unfinished tour. -/
theorem strict_moment_of_service_word {s n : Nat} (hn : 0 < n)
    (x : Raw s n) (i : Fin n) (labels : List (Fin n))
    (force : ∀ w, labels.Sublist w → publishes x i w) (t : Nat) :
    let H := 2 * n * (labels.length + 1)
    L4.Height.wordSum (fun w => 2 ^ (min (strictWait x i w) t / (8 * H))) t ≤ 2 * n ^ t := by
  let H := 2 * n * (labels.length + 1)
  have hH : 0 < H := Nat.mul_pos (Nat.mul_pos (by decide) hn) (Nat.succ_pos _)
  let hit (w : List (Fin n)) : Nat := if labels.Sublist w then 1 else 0
  let miss (w : List (Fin n)) : Nat := if labels.Sublist w then 0 else 1
  have partition : Thru.wordSum hit H + Thru.wordSum miss H = n ^ H := by
    rw [← Thru.wordSum_add_fun]
    calc
      _ = Thru.wordSum (fun _ : Thru.Word n => 1) H := by
        apply Thru.wordSum_congr
        intro w
        by_cases sub : labels.Sublist w <;> simp [hit, miss, sub]
      _ = _ := Thru.wordSum_const_one H
  have bound : PPLLOrderedWordScheduler.orderedWordMissCount labels H * 2 ≤ n ^ H :=
    PPLLOrderedWordScheduler.orderedWordMissCount_mul_twoPow_le_at_horizon labels 1
  rw [miss_indicator] at bound
  change Thru.wordSum miss H * 2 ≤ n ^ H at bound
  have enough : n ^ H ≤ 2 * Thru.wordSum hit H := by omega
  apply strict_moment_of_history_blocks x i H 2 (8 * H) hH (by decide) (by omega)
  intro v
  apply Nat.le_trans enough (Nat.mul_le_mul_left 2 ?_)
  apply Thru.wordSum_mono
  intro w
  by_cases sub : labels.Sublist w
  · have yes := force (v ++ w) (List.sublist_append_of_sublist_right sub)
    simp [hit, sub, yes]
  · simp [hit, sub]

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarFirstDoorService BStarH6Ordinal BStarClearanceOffset BStarBitSegment BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite BStarLongLiteral BStarLongPublication
open BStarBitNoAbort BStarLongLandingFrame BStarSealHealthyHop BStarAcquireAnchors BStarNeedServicePlan

open BStarAcquireRailCoverage

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
/-- A fixed raw word forces strict publication after the actual matched NEED seal. -/
theorem strict_word_after_need_seal {size n : Nat} {base origin : Raw size n} {hh : ∃ i,oldH6 (rows size) base i=true}
    {o : Owners (oldH6 (rows size) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart (show 0 < 2 by decide) base hh o S len fall) (Q : Raw size n → Prop)
    (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout (rows size) base i=BStarLongFixedRouting.Layout (rows size) x i)
    (closed : ∀ x,Q x→∀ e,Q (rawNext size x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 (rows size) base i=true)
    (own : commandOwner (oldH6 (rows size) base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal (rows size) base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner (show 0 < 2 by decide) base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := rawRun origin lead
      Q x ∧ correct (oldH6 (rows size) base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair (rows size) x i),.advance pay)∈actualOffers (oldPair (rows size) x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (ch : ∀ i, let g := longGeometry (rows size) (base i); (!g.axes.h6 || g.inside)=true)
    (ct : ∀ i, let g := oldPair (rows size) base i; continuation g.1 g.2=true) :
    ∃ labels : List (Fin n), labels.length=4*len+8 ∧ ∀ w, labels.Sublist w →
      publishes (rawNext size (rawRun origin lead) i) i w := by
  obtain ⟨labels, length, covers⟩ := BStarNeedTailService.need_tail_service_word
    (show 0 < 2 by decide) C Q fiber closed sep i k K idx head own bSite g G gateIdx ord
    lead history pay well d need oldFacts ch ct
  refine ⟨labels,length,?_⟩
  intro w sub
  obtain ⟨pre, tail, gate, side, eq, _, _, events, _⟩ := covers w sub
  refine ⟨pre, tail, eq, ?_⟩
  intro none
  let event : Publication := ⟨.left, candidate d (firstBit side)⟩
  have member := (congrArg (fun es : List Publication => event ∈ es) events).mpr
    (show event ∈ [⟨.left, candidate d (firstBit side)⟩] from List.mem_cons_self)
  exact none .left rfl event member rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
/-- Moment from the actual accepted NEED SEAL. Both the subsequent BIT
and the publishing COMMIT occur on the original raw word. -/
theorem strict_moment_after_need_seal {size n : Nat} {base origin : Raw size n} {hh : ∃ i,oldH6 (rows size) base i=true}
    {o : Owners (oldH6 (rows size) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart (show 0 < 2 by decide) base hh o S len fall) (Q : Raw size n → Prop)
    (fiber : ∀ x,Q x→∀ i,BStarLongFixedRouting.Layout (rows size) base i=BStarLongFixedRouting.Layout (rows size) x i)
    (closed : ∀ x,Q x→∀ e,Q (rawNext size x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 (rows size) base i=true)
    (own : commandOwner (oldH6 (rows size) base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal (rows size) base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner (show 0 < 2 by decide) base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := rawRun origin lead
      Q x ∧ correct (oldH6 (rows size) base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair (rows size) x i),.advance pay)∈actualOffers (oldPair (rows size) x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (ch : ∀ i, let g := longGeometry (rows size) (base i); (!g.axes.h6 || g.inside)=true)
    (ct : ∀ i, let g := oldPair (rows size) base i; continuation g.1 g.2=true) :
    ∀ t, L4.Height.wordSum
      (fun w => 2 ^ (min (strictWait (rawNext size (rawRun origin lead) i) i w) t /
        (8 * (2 * n * (4 * len + 8 + 1))))) t ≤ 2 * n ^ t := by
  obtain ⟨labels,length,covers⟩ := strict_word_after_need_seal C Q fiber closed sep i k K idx head own
    bSite g G gateIdx ord lead history pay well d need oldFacts ch ct
  intro t
  simpa only [length] using strict_moment_of_service_word (Nat.zero_lt_of_lt i.isLt)
    (rawNext size (rawRun origin lead) i) i labels covers t

#print axioms different_headers_of_publication
#print axioms singleton_publication_mass
#print axioms singleton_refutes_block
#print axioms singleton_strict_moment
#print axioms empty_center_misses
#print axioms service_moment_of_prefix_count
#print axioms block_of_strict_moment
#print axioms strict_moment_of_history_blocks
#print axioms strict_moment_after_need_seal

end
end L4.Height.RawServiceCore
