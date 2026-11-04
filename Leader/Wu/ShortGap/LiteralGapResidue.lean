import Leader.Wu.ShortGap.LiteralGapRows

/-!
# Interior residue in one literal gap

The old fourteen rows can forge a verdict from interior residue, even with
both root ports clean. This file adds one live/residue bit to declaration and
reply slots. Initial residue ranges over ALL old `Slot` values, but contains
no live marker. Only a root launch creates a live declaration; its clockwise
walk overwrites every slot ahead. The returning live reply crosses the cleared
prefix. Old slots at the right root are cleared without comparison;
elsewhere old messages wait to be overwritten. This fuses erasure and declaration,
rather than implementing a separate clear/ack traversal.

This is a different, explicitly extended pair table, not a theorem about the
old `row`. The marker exclusion at entry is essential: this is not cleanup of
arbitrary states of the extended alphabet. No root marker or unbounded epoch
is added. The bit distinguishes live traffic from the old alphabet; direction
and payload already belonged to that alphabet. No claim of global minimality
among all possible protocols is made.

Scope: interior residue only, clean root ports, one gap, general frozen choices
`c,d`, no JOIN, no pipelining. Root-port residue remains OPEN. During the sweep
the invariant must include waiting roots with an uncleared suffix: the literal
union `InteriorResidue ∪ Clean` alone is not closed. `Lane` includes precisely
these intermediate configurations as well as all starts and lifted clean
phases. Terminal projection is the original `Clean` delivered configuration.
-/

namespace ShortGapLiteralGapResidue
open ShortGapLiteralGapRows FiniteUniformStoppingTree
set_option autoImplicit false

/-- Exactly the requested old-alphabet entry condition; roots are clean and
all interior slots, including wrong declarations and replies, are arbitrary. -/
def InteriorResidue (F : Frame) (cfg : Config F) : Prop :=
  cfg (leftPos F) = .root F.c .toSend F.ccw0 ∧
  cfg (rightPos F) = .root F.d F.cw0 .free ∧
  ∀ k, 0 < k.val → k.val < F.h → ∃ s, cfg k = .interior s

/-- A two-edge gap whose true verdict is denial. -/
def forgeFrame : Frame :=
  ⟨2, by decide, .in0, .in0, Or.inr rfl, Or.inr rfl, .free, .toSend⟩

/-- A wrong outgoing declaration is initially next to the right root. -/
def forgeConfig : Config forgeFrame := fun k =>
  if k.val = 0 then .root .in0 .toSend .free
  else if k.val = 2 then .root .in0 .toSend .free
  else .interior (.decl .out1)

/-- Plain K1 forges a candidate although the held choices are `(in0,in0)`;
the owner has not launched anything. This is an actual `h=2` gap step. -/
theorem row_forges_verdict_example :
    InteriorResidue forgeFrame forgeConfig ∧
    (gapStep forgeFrame forgeConfig ⟨1, by decide⟩ (rightPos forgeFrame)).ccwPort
      = some .heldCandidate ∧
    resCcw forgeFrame.c forgeFrame.d = .heldDenial ∧
    (gapStep forgeFrame forgeConfig ⟨1, by decide⟩ (leftPos forgeFrame)).cwPort
      = some .toSend := by
  refine ⟨⟨rfl, rfl, ?_⟩, rfl, rfl, rfl⟩
  intro k h0 hh
  have hk : k.val = 1 := by change k.val < 2 at hh; omega
  exact ⟨.decl .out1, by simp [forgeConfig, hk]⟩

/-- Old agents plus live declaration/reply slots. These last two constructors
are interior states and cannot occur in the initial residue. -/
inductive EraseAgent where
  | plain (a : Agent)
  | head (c : Choice)
  | back (d : Choice)
  deriving DecidableEq

/-- Forget the live bit for comparison with the original clean predicate. -/
def project : EraseAgent → Agent
  | .plain a => a
  | .head c => .interior (.decl c)
  | .back d => .interior (.reply d)

/-- Radius-one clearing declaration. Only live heads can compare, and only
live replies can deliver. Raw declarations at a right root are discarded.
Unmatched pairs stutter. The direct root/root row handles `h=1`. -/
def rowErase : EraseAgent → EraseAgent → EraseAgent × EraseAgent
  | .plain (.root c .toSend ccw), .plain (.interior _) =>
      (.plain (.root (resolveInit c) .waiting ccw), .head (resolveInit c))
  | .plain (.root c .waiting ccw), .back d =>
      (.plain (.root c (resCw c d) ccw), .plain (.interior .empty))
  | .head c, .plain (.interior _) => (.plain (.interior .empty), .head c)
  | .head c, .plain (.root d cw .free) =>
      (.back (resolveResp d), .plain (.root (resolveResp d) cw (resCcw c (resolveResp d))))
  | .plain (.interior .empty), .back d => (.back d, .plain (.interior .empty))
  | .plain (.interior _), .plain (.root d cw ccw) =>
      (.plain (.interior .empty), .plain (.root d cw ccw))
  | .plain (.root c .toSend ccw), .plain (.root d cw .free) =>
      (.plain (.root (resolveInit c) (resCw (resolveInit c) (resolveResp d)) ccw),
        .plain (.root (resolveResp d) cw (resCcw (resolveInit c) (resolveResp d))))
  | a, b => (a, b)

abbrev EraseConfig (F : Frame) := Fin (F.h + 1) → EraseAgent

/-- Apply the new pair table to one physical edge. -/
def eraseGapStep (F : Frame) (cfg : EraseConfig F) (j : Fin F.h) : EraseConfig F :=
  fun k =>
    if k.val = j.val then (rowErase (cfg (leftEnd F j)) (cfg (rightEnd F j))).1
    else if k.val = j.val + 1 then (rowErase (cfg (leftEnd F j)) (cfg (rightEnd F j))).2
    else cfg k

/-- Explicit sweep configurations. A declaration at `j` has an empty prefix
and an arbitrary old-alphabet suffix. Return and delivered phases are clean. -/
def siteErase (F : Frame) (g : Nat → Slot) (p : Phase) (k : Nat) : EraseAgent :=
  if k = 0 then .plain (siteOf F p 0)
  else if k = F.h then .plain (siteOf F p F.h)
  else match p with
    | .prelaunch => .plain (.interior (g k))
    | .declAt j => if k = j then .head F.c
        else .plain (.interior (if j < k then g k else .empty))
    | .replyAt j => if k = j then .back F.d else .plain (.interior .empty)
    | .delivered => .plain (.interior .empty)

def eraseConfigOf (F : Frame) (g : Nat → Slot) (p : Phase) : EraseConfig F :=
  fun k => siteErase F g p k.val

/-- Background update for clearing any old slot at the right boundary.
It affects only the still-uncleared suffix, when that position is raw. -/
def nextGarbage (F : Frame) (g : Nat → Slot) (j : Fin F.h) (k : Nat) : Slot :=
  if k = j.val ∧ j.val + 1 = F.h then
    .empty
  else g k

/-- The invariant includes the intermediate sweep, not just entry/clean states. -/
def Lane (F : Frame) (cfg : EraseConfig F) : Prop :=
  ∃ p g, PhaseOk F p ∧ cfg = eraseConfigOf F g p


@[simp] theorem rowErase_plain_interiors (s t : Slot) :
    rowErase (.plain (.interior s)) (.plain (.interior t)) =
      (.plain (.interior s), .plain (.interior t)) := by cases s <;> rfl

@[simp] theorem rowErase_waiting_raw (c : Choice) (ccw : CcwPort) (s : Slot) :
    rowErase (.plain (.root c .waiting ccw)) (.plain (.interior s)) =
      (.plain (.root c .waiting ccw), .plain (.interior s)) := rfl

private theorem eraseStep_prelaunch (F : Frame) (g : Nat → Slot) (j : Fin F.h) :
    eraseGapStep F (eraseConfigOf F g .prelaunch) j =
      eraseConfigOf F (nextGarbage F g j) (nextPhase F .prelaunch j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [eraseGapStep, eraseConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> (try omega) <;> by_cases hh1 : F.h = 1 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, siteErase, siteOf, nextGarbage, hj0, hh1, hjh, hk0, hkh, hkl, hkr]
  all_goals simp [rowErase,
    resolveInit_of_base F.hc, resolveResp_of_base F.hd]

private theorem eraseStep_decl (F : Frame) (g : Nat → Slot) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) :
    eraseGapStep F (eraseConfigOf F g (.declAt t)) j =
      eraseConfigOf F (nextGarbage F g j) (nextPhase F (.declAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [eraseGapStep, eraseConfigOf, leftEnd, rightEnd]
  by_cases hjt : j.val = t <;> (try omega) <;> by_cases htlast : t + 1 = F.h <;> (try omega) <;>
    by_cases hj0 : j.val = 0 <;> (try omega) <;> by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjprev : j.val + 1 = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;> by_cases hkt1 : k.val = t + 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, siteErase, siteOf, nextGarbage, hjt, htlast, hj0, hjh, hjprev,
      hk0, hkh, hkl, hkr, hkt, hkt1, hafter]
  all_goals simp [rowErase, resolveResp_of_base F.hd]


private theorem eraseStep_reply (F : Frame) (g : Nat → Slot) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) :
    eraseGapStep F (eraseConfigOf F g (.replyAt t)) j =
      eraseConfigOf F (nextGarbage F g j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [eraseGapStep, eraseConfigOf, leftEnd, rightEnd]
  by_cases hjprev : j.val + 1 = t <;> (try omega) <;>
    by_cases ht1 : t = 1 <;> (try omega) <;>
    by_cases hj0 : j.val = 0 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjt : j.val = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;>
      by_cases hktprev : k.val = t - 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, siteErase, siteOf, hjprev, ht1, hj0, hjh, hjt,
      hk0, hkh, hkl, hkr, hkt, hktprev]
  all_goals
    cases hv : res F.c F.d <;>
      simp [rowErase, resCw, resCcw, hv,
        Verdict.cw, Verdict.ccw]

private theorem eraseStep_delivered (F : Frame) (g : Nat → Slot) (j : Fin F.h) :
    eraseGapStep F (eraseConfigOf F g .delivered) j =
      eraseConfigOf F (nextGarbage F g j) (nextPhase F .delivered j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [eraseGapStep, eraseConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, siteErase, siteOf, hj0, hjh, hk0, hkh, hkl, hkr]
  all_goals
    cases hv : res F.c F.d <;>
      simp [rowErase, resCw, resCcw, hv,
        Verdict.cw, Verdict.ccw]

/-- Exact physical-row simulation. The old phase clock remains valid even
while the uncleared suffix contains arbitrary old messages. -/
theorem eraseGapStep_configOf (F : Frame) (g : Nat → Slot)
    (p : Phase) (hp : PhaseOk F p) (j : Fin F.h) :
    eraseGapStep F (eraseConfigOf F g p) j =
      eraseConfigOf F (nextGarbage F g j) (nextPhase F p j) := by
  cases p with
  | prelaunch => exact eraseStep_prelaunch F g j
  | declAt t => exact eraseStep_decl F g t hp.1 hp.2 j
  | replyAt t => exact eraseStep_reply F g t hp.1 hp.2 j
  | delivered => exact eraseStep_delivered F g j


/-- Ignore raw interior residue only for reading the phase debt. This map is
not the physical step; its commutation with the actual rows is proved below. -/
def skeletonAgent : EraseAgent → Agent
  | .plain (.interior _) => .interior .empty
  | a => project a

def skeleton (F : Frame) (cfg : EraseConfig F) : Config F :=
  fun k => skeletonAgent (cfg k)

/-- Removing raw residue from a sweep configuration gives the original clean
phase exactly, with the same two held choices and ports. -/
theorem skeleton_configOf (F : Frame) (g : Nat → Slot)
    (p : Phase) (hp : PhaseOk F p) :
    skeleton F (eraseConfigOf F g p) = configOf F p := by
  have hh := F.hpos
  funext k
  have hk := k.isLt
  by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
  all_goals cases p with
  | prelaunch =>
    simp (disch := omega) [if_neg, skeleton, eraseConfigOf, configOf,
      siteErase, siteOf, skeletonAgent, project, h0, hlast]
  | delivered =>
    simp (disch := omega) [if_neg, skeleton, eraseConfigOf, configOf,
      siteErase, siteOf, skeletonAgent, project, h0, hlast]
  | declAt t =>
    by_cases ht : k.val = t <;>
      simp (disch := omega) [if_pos, if_neg, skeleton, eraseConfigOf, configOf,
        siteErase, siteOf, skeletonAgent, project, h0, hlast, ht]
  | replyAt t =>
    by_cases ht : k.val = t <;>
      simp (disch := omega) [if_pos, if_neg, skeleton, eraseConfigOf, configOf,
        siteErase, siteOf, skeletonAgent, project, h0, hlast, ht]


/-- Lift an already authenticated clean token by setting its live bit.
This differs deliberately from `embedResidue`, which marks nothing as live. -/
def liftCleanAgent : Agent → EraseAgent
  | .interior (.decl c) => .head c
  | .interior (.reply d) => .back d
  | a => .plain a

def liftClean (F : Frame) (cfg : Config F) : EraseConfig F := fun k => liftCleanAgent (cfg k)

theorem liftClean_configOf (F : Frame) (p : Phase) :
    liftClean F (configOf F p) = eraseConfigOf F (fun _ => .empty) p := by
  have hh := F.hpos
  funext k
  by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
  all_goals cases p with
  | prelaunch =>
    simp (disch := omega) [if_neg, liftClean, liftCleanAgent, eraseConfigOf, configOf,
      siteErase, siteOf, h0, hlast]
  | delivered =>
    simp (disch := omega) [if_neg, liftClean, liftCleanAgent, eraseConfigOf, configOf,
      siteErase, siteOf, h0, hlast]
  | declAt t =>
    by_cases ht : k.val = t <;>
      simp (disch := omega) [if_neg, liftClean, liftCleanAgent, eraseConfigOf, configOf,
        siteErase, siteOf, h0, hlast, ht]
  | replyAt t =>
    by_cases ht : k.val = t <;>
      simp (disch := omega) [if_neg, liftClean, liftCleanAgent, eraseConfigOf, configOf,
        siteErase, siteOf, h0, hlast, ht]

/-- All authenticated clean configurations belong to the invariant, alongside
all arbitrary old-alphabet residue entries and intermediate sweep states. -/
theorem clean_lane (F : Frame) (cfg : Config F) (hc : Clean F cfg) :
    Lane F (liftClean F cfg) := by
  obtain ⟨p, hp, rfl⟩ := hc.exists_phase
  exact ⟨p, (fun _ => .empty), hp, liftClean_configOf F p⟩

/-- Every physical edge preserves the sweep invariant. -/
theorem lane_gapStep (F : Frame) (cfg : EraseConfig F)
    (hl : Lane F cfg) (j : Fin F.h) : Lane F (eraseGapStep F cfg j) := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  exact ⟨nextPhase F p j, nextGarbage F g j,
    nextPhase_phaseOk F p hp j, eraseGapStep_configOf F g p hp j⟩

/-- All lane configurations have a clean phase skeleton. -/
theorem skeleton_clean (F : Frame) (cfg : EraseConfig F) (hl : Lane F cfg) :
    Clean F (skeleton F cfg) := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  rw [skeleton_configOf F g p hp]
  exact Clean.of_phaseOk F p hp

/-- Non-masking of the phase clock is derived from the extended pair rows. -/
theorem skeleton_gapStep (F : Frame) (cfg : EraseConfig F)
    (hl : Lane F cfg) (j : Fin F.h) :
    skeleton F (eraseGapStep F cfg j) = gapStep F (skeleton F cfg) j := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  rw [eraseGapStep_configOf F g p hp j,
    skeleton_configOf F _ _ (nextPhase_phaseOk F p hp j),
    skeleton_configOf F g p hp, gapStep_configOf F p hp j]

open Classical in
/-- Scheduler edges outside the embedding stutter, exactly as in the base gap. -/
noncomputable def eraseSchedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (e : Fin n) : EraseConfig F :=
  if hx : ∃ j : Fin F.h, E.edgeAt j = e then eraseGapStep F cfg hx.choose else cfg

theorem eraseSchedStep_eq {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (j : Fin F.h) :
    eraseSchedStep F E cfg (E.edgeAt j) = eraseGapStep F cfg j := by
  classical
  have hx : ∃ a, E.edgeAt a = E.edgeAt j := ⟨j, rfl⟩
  rw [eraseSchedStep, dif_pos hx, E.inj _ _ hx.choose_spec]

theorem lane_schedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : Lane F cfg) (e : Fin n) :
    Lane F (eraseSchedStep F E cfg e) := by
  classical
  unfold eraseSchedStep
  split
  · exact lane_gapStep F cfg hl _
  · exact hl

theorem skeleton_schedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : Lane F cfg) (e : Fin n) :
    skeleton F (eraseSchedStep F E cfg e) = schedStep F E (skeleton F cfg) e := by
  classical
  unfold eraseSchedStep schedStep
  split
  · exact skeleton_gapStep F cfg hl _
  · rfl

/-- Unscaled residue debt: the unique live sweep pays for overwriting the
entire suffix, so no separate garbage-count credit is necessary. -/
def residueDebt (F : Frame) (cfg : EraseConfig F) : Nat := deltaOf F (skeleton F cfg)

theorem residueDebt_configOf (F : Frame) (g : Nat → Slot)
    (p : Phase) (hp : PhaseOk F p) :
    residueDebt F (eraseConfigOf F g p) = phaseDebt F p := by
  rw [residueDebt, skeleton_configOf F g p hp, deltaOf_configOf F p hp]

/-- Every nonterminal lane state has the base one-gap child-sum decrease. -/
theorem residue_childSum {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : Lane F cfg) (hp : 0 < residueDebt F cfg) :
    1 + (List.ofFn (fun e : Fin n => residueDebt F (eraseSchedStep F E cfg e))).sum
      ≤ n * residueDebt F cfg := by
  have h := delta_childSum F E (skeleton F cfg) (skeleton_clean F cfg hl) hp
  simpa only [residueDebt, skeleton_schedStep F E cfg hl] using h

/-- Physical lane configurations with positive residue debt. -/
def ActiveResidue (F : Frame) := {cfg : EraseConfig F // Lane F cfg ∧ 0 < residueDebt F cfg}

/-- Stop precisely at zero debt. A zero-debt lane state is proved delivered
below, so this stopping test cannot declare dirty success. -/
noncomputable def residueNode {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveResidue F) (e : Fin n) : StopNode (ActiveResidue F) :=
  if hp : 0 < residueDebt F (eraseSchedStep F E s.1 e) then
    .active ⟨eraseSchedStep F E s.1 e, lane_schedStep F E s.1 s.2.1 e, hp⟩
  else .success

/-- Scale-one potential, measured in scheduler interactions, is `ρ = n*debt`. -/
def residuePotential {n : Nat} (F : Frame) : StopNode (ActiveResidue F) → Nat
  | .active s => n * residueDebt F s.1
  | _ => 0

private theorem residuePotential_node {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveResidue F) (e : Fin n) :
    residuePotential (n := n) F (residueNode F E s e) =
      n * residueDebt F (eraseSchedStep F E s.1 e) := by
  unfold residueNode
  split
  · rfl
  · rename_i hz
    have hd : residueDebt F (eraseSchedStep F E s.1 e) = 0 := by omega
    simp [residuePotential, hd]

/-- Bellman convergence certificate for the actual extended pair table,
including all intermediate residue configurations, with scale exactly one. -/
theorem residue_natBellmanSuperSolution {n : Nat} (F : Frame) (E : GapEmbedding F n) :
    NatBellmanSuperSolution (residueNode F E) 1 (residuePotential (n := n) F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have h := Nat.mul_le_mul_left n (residue_childSum F E s.1 s.2.1 s.2.2)
  have he : (List.ofFn (fun e : Fin n => residuePotential (n := n) F
      (residueNode F E s e))).sum =
      n * (List.ofFn (fun e : Fin n => residueDebt F (eraseSchedStep F E s.1 e))).sum := by
    rw [← ofFn_sum_mul_left]
    exact ofFn_sum_eq _ _ (fun e => residuePotential_node F E s e)
  rw [he]
  simpa only [Nat.mul_add, Nat.mul_one, Nat.one_mul, residuePotential] using h


/-- Read arbitrary old interior slots; endpoint and out-of-range values are
irrelevant to the prelaunch representation. -/
def garbageOf (F : Frame) (cfg : Config F) (k : Nat) : Slot :=
  if hk : k < F.h + 1 then
    match cfg ⟨k, hk⟩ with | .interior s => s | _ => .empty
  else .empty

/-- Embed an old-alphabet configuration without granting any message a live bit. -/
def embedResidue (F : Frame) (cfg : Config F) : EraseConfig F :=
  fun k => .plain (cfg k)

/-- Every requested entry is covered, not just a chosen garbage pattern. -/
theorem interiorResidue_representation (F : Frame) (cfg : Config F)
    (hi : InteriorResidue F cfg) :
    embedResidue F cfg = eraseConfigOf F (garbageOf F cfg) .prelaunch := by
  have hh := F.hpos
  funext k
  have hk := k.isLt
  by_cases hk0 : k.val = 0
  · have he : k = leftPos F := Fin.ext hk0
    subst k
    change EraseAgent.plain (cfg (leftPos F)) = .plain (.root F.c .toSend F.ccw0)
    exact congrArg EraseAgent.plain hi.1
  · by_cases hkh : k.val = F.h
    · have he : k = rightPos F := Fin.ext hkh
      subst k
      change EraseAgent.plain (cfg (rightPos F)) = siteErase F (garbageOf F cfg) .prelaunch F.h
      rw [hi.2.1]
      simp (disch := omega) [if_neg, siteErase, siteOf]
    · obtain ⟨s, hs⟩ := hi.2.2 k (by omega) (by omega)
      simp [embedResidue, eraseConfigOf, siteErase, hk0, hkh, garbageOf, hk, hs]

theorem interiorResidue_lane (F : Frame) (cfg : Config F) (hi : InteriorResidue F cfg) :
    Lane F (embedResidue F cfg) :=
  ⟨.prelaunch, garbageOf F cfg, trivial, interiorResidue_representation F cfg hi⟩

/-- The exact debt at every arbitrary-residue start is `2h-1`. -/
theorem residueDebt_start (F : Frame) (cfg : Config F) (hi : InteriorResidue F cfg) :
    residueDebt F (embedResidue F cfg) = 2 * F.h - 1 := by
  rw [interiorResidue_representation F cfg hi, residueDebt_configOf F _ .prelaunch trivial]
  rfl

/-- Every phase has at most the prelaunch debt. -/
theorem residueDebt_le (F : Frame) (cfg : EraseConfig F) (hl : Lane F cfg) :
    residueDebt F cfg ≤ 2 * F.h - 1 := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  rw [residueDebt_configOf F g p hp]
  have hh := F.hpos
  cases p <;> simp only [phaseDebt, PhaseOk] at * <;> omega

/-- Zero debt cannot conceal a dirty suffix: only the delivered phase has
zero debt, and that phase has no residue anywhere. -/
theorem residue_zero_delivered (F : Frame) (cfg : EraseConfig F)
    (hl : Lane F cfg) (hz : residueDebt F cfg = 0) :
    (fun k => project (cfg k)) = configOf F .delivered := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  rw [residueDebt_configOf F g p hp] at hz
  have hh := F.hpos
  have hphase : p = .delivered := by
    cases p <;> simp only [PhaseOk, phaseDebt] at * <;> first | rfl | omega
  subst p
  funext k
  by_cases h0 : k.val = 0 <;> by_cases hh : k.val = F.h <;>
    simp (disch := omega) [if_neg, eraseConfigOf, siteErase, configOf, siteOf, project, h0, hh]

/-- Lane-level authentication: the right root holds either no verdict or the
correct verdict of the actual held choices; every live head has the owner
payload. Thus a wrong garbage payload cannot become an accepted live head. -/
theorem lane_authentic (F : Frame) (cfg : EraseConfig F) (hl : Lane F cfg) :
    ((project (cfg (rightPos F))).ccwPort = some .free ∨
      (project (cfg (rightPos F))).ccwPort = some (resCcw F.c F.d)) ∧
    (∀ k c0, cfg k = .head c0 → c0 = F.c) ∧
    (∀ k d0, cfg k = .back d0 → d0 = F.d) := by
  obtain ⟨p, g, hp, rfl⟩ := hl
  have hh := F.hpos
  constructor
  · cases p <;>
      simp (disch := omega) [if_neg, eraseConfigOf, siteErase,
        siteOf, rightPos, project, Agent.ccwPort]
  · constructor
    · intro k c0 he
      by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
      all_goals cases p <;> simp_all [eraseConfigOf, siteErase]
      all_goals split at he <;> simp_all
    · intro k d0 he
      by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
      all_goals cases p <;> simp_all [eraseConfigOf, siteErase]
      all_goals split at he <;> simp_all

/-- The local garbage-discard row does not inspect or change the right verdict. -/
theorem rowErase_discards_garbage (c0 d : Choice) (cw : CwPort) (ccw : CcwPort) :
    rowErase (.plain (.interior (.decl c0))) (.plain (.root d cw ccw)) =
      (.plain (.interior .empty), .plain (.root d cw ccw)) := rfl

/-- Run a finite word of actual scheduler edges. -/
noncomputable def eraseRun {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) : List (Fin n) → EraseConfig F
  | [] => cfg
  | e :: es => eraseRun F E (eraseSchedStep F E cfg e) es

theorem lane_run {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : Lane F cfg) (es : List (Fin n)) :
    Lane F (eraseRun F E cfg es) := by
  induction es generalizing cfg with
  | nil => exact hl
  | cons e es ih => exact ih _ (lane_schedStep F E cfg hl e)

/-- No garbage-derived verdict at any finite reachable state, for every
allowed old-alphabet residue and every schedule. The marker payload clauses
state the live-lineage fact as well as correctness of the visible verdict. -/
theorem no_forged_verdict {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : InteriorResidue F cfg) (es : List (Fin n)) :
    let out := eraseRun F E (embedResidue F cfg) es
    ((project (out (rightPos F))).ccwPort = some .free ∨
      (project (out (rightPos F))).ccwPort = some (resCcw F.c F.d)) ∧
    (∀ k c0, out k = .head c0 → c0 = F.c) ∧
    (∀ k d0, out k = .back d0 → d0 = F.d) := by
  exact lane_authentic F _ (lane_run F E _ (interiorResidue_lane F cfg hi) es)


/-- The stopped process has no failure branch. -/
theorem residueNode_ne_failure {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveResidue F) (e : Fin n) : residueNode F E s e ≠ .failure := by
  unfold residueNode
  split <;> simp

/-- A successful stopping edge really leaves the original delivered clean
configuration, including empty interior slots and both matching receipts. -/
theorem residue_success_delivered {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveResidue F) (e : Fin n) (hs : residueNode F E s e = .success) :
    (fun k => project (eraseSchedStep F E s.1 e k)) = configOf F .delivered := by
  apply residue_zero_delivered F _ (lane_schedStep F E s.1 s.2.1 e)
  unfold residueNode at hs
  split at hs
  · contradiction
  · omega

private theorem lane_reaches_in {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (D : Nat) : ∀ cfg : EraseConfig F, Lane F cfg → residueDebt F cfg ≤ D →
    ∃ es : List (Fin n), es.length ≤ D ∧
      (fun k => project (eraseRun F E cfg es k)) = configOf F .delivered := by
  induction D with
  | zero =>
    intro cfg hl hd
    exact ⟨[], Nat.le_refl 0, residue_zero_delivered F cfg hl (by omega)⟩
  | succ D ih =>
    intro cfg hl hd
    by_cases hz : residueDebt F cfg = 0
    · exact ⟨[], Nat.zero_le _, residue_zero_delivered F cfg hl hz⟩
    · have hp : 0 < residueDebt F cfg := by omega
      obtain ⟨a, ha⟩ := delta_useful_lt F E (skeleton F cfg) (skeleton_clean F cfg hl) hp
      have hdrop : residueDebt F (eraseSchedStep F E cfg (E.edgeAt a)) + 1 =
          residueDebt F cfg := by
        simpa only [residueDebt, skeleton_schedStep F E cfg hl] using ha
      obtain ⟨es, hlen, hend⟩ := ih (eraseSchedStep F E cfg (E.edgeAt a))
        (lane_schedStep F E cfg hl _) (by omega)
      refine ⟨E.edgeAt a :: es, ?_, hend⟩
      simp only [List.length_cons]
      omega

/-- Constructive reachability, separate from the probabilistic Bellman claim:
from every allowed residue there exists a schedule of at most `2h-1` useful
firings leading to the original delivered `Clean` state. Arbitrary schedules
need not terminate; the finite-horizon bound accounts for scheduler stutters. -/
theorem residue_reaches_clean {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : InteriorResidue F cfg) :
    ∃ es : List (Fin n), es.length ≤ 2 * F.h - 1 ∧
      (fun k => project (eraseRun F E (embedResidue F cfg) es k)) = configOf F .delivered ∧
      Clean F (fun k => project (eraseRun F E (embedResidue F cfg) es k)) := by
  obtain ⟨es, hlen, hend⟩ := lane_reaches_in F E (2 * F.h - 1)
    (embedResidue F cfg) (interiorResidue_lane F cfg hi)
    (Nat.le_of_eq (residueDebt_start F cfg hi))
  exact ⟨es, hlen, hend, hend ▸ Clean.delivered⟩

/-- Every residue entry has positive debt because `h≥1`. -/
def residueStart (F : Frame) (cfg : Config F) (hi : InteriorResidue F cfg) : ActiveResidue F :=
  ⟨embedResidue F cfg, interiorResidue_lane F cfg hi, by
    rw [residueDebt_start F cfg hi]
    have hh := F.hpos
    omega⟩

/-- Exact scaled start bound; it is stronger than the requested `n*(4h-3)`
because this trusted-entry variant fuses the clearing head with declaration. -/
theorem residuePotential_start {n : Nat} (F : Frame) (cfg : Config F)
    (hi : InteriorResidue F cfg) :
    residuePotential (n := n) F (.active (residueStart F cfg hi)) = n * (2 * F.h - 1) ∧
    residuePotential (n := n) F (.active (residueStart F cfg hi)) ≤ n * (4 * F.h - 3) := by
  have he : residuePotential (n := n) F (.active (residueStart F cfg hi)) =
      n * (2 * F.h - 1) := by
    change n * residueDebt F (embedResidue F cfg) = _
    rw [residueDebt_start F cfg hi]
  refine ⟨he, ?_⟩
  rw [he]
  apply Nat.mul_le_mul_left
  have hh := F.hpos
  omega

/-- Quantitative convergence: every truncated active-cost numerator is bounded
by the same start potential, uniformly in the horizon. Together with the
zero-debt delivery theorem this is the scale-one stopped-process certificate. -/
theorem residue_converges {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : InteriorResidue F cfg) (T : Nat) :
    truncatedActiveCostNumerator (residueNode F E) (.active (residueStart F cfg hi)) T
      ≤ n ^ T * (n * (2 * F.h - 1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (residueNode F E) 1 (residuePotential (n := n) F)
    (residue_natBellmanSuperSolution F E) (.active (residueStart F cfg hi)) T
  simpa only [Nat.one_mul, (residuePotential_start (n := n) F cfg hi).1] using h


/-- Division-free reciprocal tail: normalized unfinished mass is at most
`n*(2h-1)/T` for every positive horizon, with no asymptotic or independence
assumption hidden in the bound. -/
theorem residue_tail {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : InteriorResidue F cfg) (T : Nat) :
    T * activeCount (residueNode F E) (.active (residueStart F cfg hi)) T
      ≤ n ^ T * (n * (2 * F.h - 1)) :=
  Nat.le_trans (horizon_mul_activeCount_le_truncatedActiveCostNumerator
    (residueNode F E) (.active (residueStart F cfg hi)) T)
    (residue_converges F E cfg hi T)


/-- A three-edge witness showing why entry/clean union alone is not invariant. -/
def sweepFrame : Frame :=
  ⟨3, by decide, .in0, .in0, Or.inr rfl, Or.inr rfl, .free, .toSend⟩

/-- The first live declaration leaves one old declaration still ahead. -/
def sweepWitness : EraseConfig sweepFrame :=
  eraseConfigOf sweepFrame (fun _ => .decl .out1) (.declAt 1)

/-- This witness really is produced by the first edge, not an unreachable
extra case introduced solely to inflate the invariant. -/
theorem sweepWitness_reached :
    eraseGapStep sweepFrame (eraseConfigOf sweepFrame (fun _ => .decl .out1) .prelaunch)
      ⟨0, by decide⟩ = sweepWitness := by
  have hg : nextGarbage sweepFrame (fun _ => .decl .out1) ⟨0, by decide⟩ =
      (fun _ => .decl .out1) := by
    funext k
    simp [nextGarbage, sweepFrame]
  rw [eraseGapStep_configOf sweepFrame _ .prelaunch trivial, hg]
  rfl

/-- A reachable sweep state is neither a clean-root residue entry nor a clean
phase. The required invariant enlargement is therefore mathematically necessary. -/
theorem entry_clean_union_not_closed :
    ¬ InteriorResidue sweepFrame (fun k => project (sweepWitness k)) ∧
    ¬ Clean sweepFrame (fun k => project (sweepWitness k)) := by
  constructor
  · intro hi
    have he := hi.1
    contradiction
  · intro hc
    obtain ⟨p, hp, he⟩ := hc.exists_phase
    have h0 := congrFun he ⟨0, by decide⟩
    have h1 := congrFun he ⟨1, by decide⟩
    have h2 := congrFun he ⟨2, by decide⟩
    cases p with
    | prelaunch => contradiction
    | delivered => contradiction
    | declAt t =>
      by_cases ht : t = 1 <;> by_cases ht2 : t = 2 <;>
        simp_all [sweepWitness, sweepFrame, eraseConfigOf, siteErase, configOf, siteOf,
          project, PhaseOk]
    | replyAt t =>
      change Agent.interior (.decl .in0) =
        (if 1 = t then Agent.interior (.reply .in0) else Agent.interior .empty) at h1
      split at h1 <;> contradiction

#print axioms residue_reaches_clean
#print axioms row_forges_verdict_example
#print axioms residue_natBellmanSuperSolution
#print axioms residue_converges
#print axioms no_forged_verdict

end ShortGapLiteralGapResidue
