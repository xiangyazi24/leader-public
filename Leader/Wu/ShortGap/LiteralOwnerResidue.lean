import Leader.Wu.ShortGap.LiteralGapResidue

/-!
# A stuck waiting owner: timeout-free re-declaration

Root-port residue case (1) only: the owner is `waiting`, the right root is
`free`, and every interior slot is an arbitrary UNMARKED old slot. General
frozen endpoint choices and arbitrary framed opposite ports are retained.
One gap, no JOIN, no pipelining. Detached/forged held-candidate ports and
forged live markers remain OPEN and are excluded from this entry predicate.

No additional alphabet is needed beyond `EraseAgent`. A waiting owner sends
another live declaration whenever its first slot is unmarked. The guard
cannot detect a live token deeper in the gap. Duplicates are therefore real:
forward heads coalesce, and a returning reply WINS every collision with a
head. The leading head clears the arbitrary suffix; its unique reply clears
all duplicate heads to its left. No token can cross that reply. The right
root compares exactly once in a completed service, and the delivered state
has empty interiors, including no leftover duplicates.

`OwnerLane` records a leading head or unique reply, with arbitrary duplicate
heads in its prefix. This is an explicit invariant of the pair table, not a
uniqueness assumption about all tokens. The physical debt is the minimum of
live-token countdowns and the initial countdown `2h-1`; duplicate injection
cannot increase that minimum. The phase simulation proves the exact debt
clock and the scale-one Bellman certificate.
-/

namespace ShortGapLiteralOwnerResidue
open ShortGapLiteralGapRows ShortGapLiteralGapResidue FiniteUniformStoppingTree
set_option autoImplicit false

/-- Root ports otherwise clean; no live marker exists at entry. -/
def OwnerStuck (F : Frame) (cfg : Config F) : Prop :=
  cfg (leftPos F) = .root F.c .waiting F.ccw0 ∧
  cfg (rightPos F) = .root F.d F.cw0 .free ∧
  ∀ k, 0 < k.val → k.val < F.h → ∃ s, cfg k = .interior s

/-- A radius-one repair. The waiting owner may inject duplicates. Replies
absorb heads, forward heads coalesce, and only a free right port can compare.
Raw messages cannot compare or deliver. All unmatched pairs stutter. -/
def rowRedeclare : EraseAgent → EraseAgent → EraseAgent × EraseAgent
  | .plain (.root c .waiting ccw), .plain (.interior _) =>
      (.plain (.root (resolveInit c) .waiting ccw), .head (resolveInit c))
  | .plain (.root c .waiting ccw), .back d =>
      (.plain (.root c (resCw c d) ccw), .plain (.interior .empty))
  | .head c, .plain (.interior _) => (.plain (.interior .empty), .head c)
  | .head _, .head c => (.plain (.interior .empty), .head c)
  | .head _, .back d => (.back d, .plain (.interior .empty))
  | .plain (.interior _), .back d => (.back d, .plain (.interior .empty))
  | .head c, .plain (.root d cw .free) =>
      (.back (resolveResp d), .plain (.root (resolveResp d) cw (resCcw c (resolveResp d))))
  | .plain (.interior _), .plain (.root d cw ccw) =>
      (.plain (.interior .empty), .plain (.root d cw ccw))
  | .plain (.root c .waiting ccw), .plain (.root d cw .free) =>
      (.plain (.root (resolveInit c) (resCw (resolveInit c) (resolveResp d)) ccw),
        .plain (.root (resolveResp d) cw (resCcw (resolveInit c) (resolveResp d))))
  | a, b => (a, b)

/-- Scheduled update of exactly the two physical endpoints. -/
def ownerGapStep (F : Frame) (cfg : EraseConfig F) (j : Fin F.h) : EraseConfig F :=
  fun k =>
    if k.val = j.val then (rowRedeclare (cfg (leftEnd F j)) (cfg (rightEnd F j))).1
    else if k.val = j.val + 1 then (rowRedeclare (cfg (leftEnd F j)) (cfg (rightEnd F j))).2
    else cfg k

/-- A cleared prefix can contain any number of duplicate live heads. -/
def prefixSite (F : Frame) (b : Bool) : EraseAgent :=
  if b then .head F.c else .plain (.interior .empty)

def ownerPort (F : Frame) : Phase → CwPort
  | .delivered => resCw F.c F.d
  | _ => .waiting

/-- Explicit phase configurations: before launch there is only raw residue;
a leading head has raw residue ahead and duplicate heads behind; the unique
reply has only empty slots to its right and duplicate heads to its left. -/
def ownerSite (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (p : Phase) (k : Nat) : EraseAgent :=
  if k = 0 then .plain (.root F.c (ownerPort F p) F.ccw0)
  else if k = F.h then .plain (siteOf F p F.h)
  else match p with
    | .prelaunch => .plain (.interior (g k))
    | .declAt t => if k = t then .head F.c
        else if t < k then .plain (.interior (g k)) else prefixSite F (b k)
    | .replyAt t => if k = t then .back F.d
        else if t < k then .plain (.interior .empty) else prefixSite F (b k)
    | .delivered => .plain (.interior .empty)

def ownerConfigOf (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (p : Phase) : EraseConfig F :=
  fun k => ownerSite F g b p k.val

/-- Boolean bookkeeping of duplicate heads; only positions strictly behind
the distinguished token are read, so frontier/suffix bits are irrelevant. -/
def nextBits {h : Nat} (b : Nat → Bool) (j : Fin h) (k : Nat) : Bool :=
  if k = j.val then false
  else if k = j.val + 1 then decide (j.val = 0) || b j.val || b (j.val + 1)
  else b k

/-- The complete repair invariant, including multiple live declarations. -/
def OwnerLane (F : Frame) (cfg : EraseConfig F) : Prop :=
  ∃ p g b, PhaseOk F p ∧ cfg = ownerConfigOf F g b p

@[simp] theorem rowRedeclare_plain_interiors (s t : Slot) :
    rowRedeclare (.plain (.interior s)) (.plain (.interior t)) =
      (.plain (.interior s), .plain (.interior t)) := rfl
private theorem ownerStep_prelaunch (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (j : Fin F.h) :
    ownerGapStep F (ownerConfigOf F g b .prelaunch) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F .prelaunch j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> (try omega) <;> by_cases hh1 : F.h = 1 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, nextGarbage, hj0, hh1, hjh, hk0, hkh, hkl, hkr]
  all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;> simp_all [rowRedeclare,
    resolveInit_of_base F.hc, resolveResp_of_base F.hd]

private theorem ownerStep_decl_yes_root (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (_hth : t < F.h) (j : Fin F.h) (hjt : j.val = t) (hj0 : j.val = 0) :
    ownerGapStep F (ownerConfigOf F g b (.declAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.declAt t) j) := by
  omega

private theorem ownerStep_decl_yes_inner (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjt : j.val = t) (hj0 : j.val ≠ 0) :
    ownerGapStep F (ownerConfigOf F g b (.declAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.declAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases htlast : t + 1 = F.h <;> (try omega) <;>
     by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjprev : j.val + 1 = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;> by_cases hkt1 : k.val = t + 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, nextGarbage, hjt, htlast, hj0, hjh, hjprev,
      hk0, hkh, hkl, hkr, hkt, hkt1, hafter]
  all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;> simp_all [rowRedeclare, resolveInit_of_base F.hc, resolveResp_of_base F.hd]



private theorem ownerStep_decl_no_root (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjt : ¬ (j.val = t)) (hj0 : j.val = 0) :
    ownerGapStep F (ownerConfigOf F g b (.declAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.declAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases htlast : t + 1 = F.h <;> (try omega) <;>
     by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjprev : j.val + 1 = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;> by_cases hkt1 : k.val = t + 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, nextGarbage, hjt, htlast, hj0, hjh, hjprev,
      hk0, hkh, hkl, hkr, hkt, hkt1, hafter]
  all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;> simp_all [rowRedeclare, resolveInit_of_base F.hc, resolveResp_of_base F.hd]



private theorem ownerStep_decl_no_inner (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjt : ¬ (j.val = t)) (hj0 : j.val ≠ 0) :
    ownerGapStep F (ownerConfigOf F g b (.declAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.declAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases htlast : t + 1 = F.h <;> (try omega) <;>
     by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjprev : j.val + 1 = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;> by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;> by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;> by_cases hkt1 : k.val = t + 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, nextGarbage, hjt, htlast, hj0, hjh, hjprev,
      hk0, hkh, hkl, hkr, hkt, hkt1, hafter]
  all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;> simp_all [rowRedeclare, resolveInit_of_base F.hc, resolveResp_of_base F.hd]


private theorem ownerStep_decl (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) :
    ownerGapStep F (ownerConfigOf F g b (.declAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.declAt t) j) := by
  by_cases hjt : j.val = t <;> by_cases hj0 : j.val = 0
  · exact ownerStep_decl_yes_root F g b t ht0 hth j hjt hj0
  · exact ownerStep_decl_yes_inner F g b t ht0 hth j hjt hj0
  · exact ownerStep_decl_no_root F g b t ht0 hth j hjt hj0
  · exact ownerStep_decl_no_inner F g b t ht0 hth j hjt hj0


private theorem ownerStep_reply_yes_root (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : j.val + 1 = t) (hj0 : j.val = 0) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
 
  by_cases ht1 : t = 1 <;> (try omega) <;>
    
    by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjt : j.val = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;>
      by_cases hktprev : k.val = t - 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, hjprev, ht1, hj0, hjh, hjt,
      hk0, hkh, hkl, hkr, hkt, hktprev, hafter]
  all_goals
    cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      simp_all [rowRedeclare, resolveInit_of_base F.hc]


private theorem ownerStep_reply_yes_inner (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : j.val + 1 = t) (hj0 : j.val ≠ 0) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
 
  by_cases ht1 : t = 1 <;> (try omega) <;>
    
    by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjt : j.val = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;>
      by_cases hktprev : k.val = t - 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, hjprev, ht1, hj0, hjh, hjt,
      hk0, hkh, hkl, hkr, hkt, hktprev, hafter]
  all_goals
    cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      simp_all [rowRedeclare, resolveInit_of_base F.hc]


private theorem ownerStep_reply_no_root (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : ¬ (j.val + 1 = t)) (hj0 : j.val = 0) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
 
  by_cases ht1 : t = 1 <;> (try omega) <;>
    
    by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    by_cases hjt : j.val = t <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;>
      by_cases hktprev : k.val = t - 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, hjprev, ht1, hj0, hjh, hjt,
      hk0, hkh, hkl, hkr, hkt, hktprev, hafter]
  all_goals
    cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      simp_all [rowRedeclare, resolveInit_of_base F.hc]


private theorem ownerStep_reply_no_inner_back (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : ¬ (j.val + 1 = t)) (hj0 : j.val ≠ 0) (hjt : j.val = t) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
 
  by_cases ht1 : t = 1 <;> (try omega) <;>
    
    by_cases hjh : j.val + 1 = F.h <;> (try omega) <;>
    try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> (try omega) <;>
      by_cases hkt : k.val = t <;> (try omega) <;>
      by_cases hktprev : k.val = t - 1 <;> (try omega) <;>
      by_cases hafter : t < k.val <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, hjprev, ht1, hj0, hjh, hjt,
      hk0, hkh, hkl, hkr, hkt, hktprev, hafter]
  all_goals
    cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      simp_all [rowRedeclare, resolveInit_of_base F.hc]


/-- Pointwise framing avoids enumerating unrelated sites in a local update. -/
private theorem ownerSite_congr (F : Frame) (g g' : Nat → Slot) (b b' : Nat → Bool)
    (p : Phase) (k : Nat) (hg : g k = g' k) (hb : b k = b' k) :
    ownerSite F g b p k = ownerSite F g' b' p k := by
  cases p <;> simp [ownerSite, hg, hb]

private theorem rowRedeclare_prefix (F : Frame) (u v : Bool) :
    rowRedeclare (prefixSite F u) (prefixSite F v) =
      (.plain (.interior .empty), prefixSite F (u || v)) := by
  cases u <;> cases v <;> rfl

private theorem ownerStep_reply_no_inner_other (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : ¬ (j.val + 1 = t)) (hj0 : j.val ≠ 0) (hjt : j.val ≠ t) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  have hh := F.hpos
  have hj := j.isLt
  have hnext : nextPhase F (.replyAt t) j = .replyAt t := by simp [nextPhase, hjprev]
  rw [hnext]
  by_cases hbefore : j.val < t
  · have hbef : j.val + 1 < t := by omega
    have hrow : rowRedeclare
        (ownerConfigOf F g b (.replyAt t) (leftEnd F j))
        (ownerConfigOf F g b (.replyAt t) (rightEnd F j)) =
        (.plain (.interior .empty), prefixSite F (b j.val || b (j.val + 1))) := by
      dsimp +instances only [ownerConfigOf, leftEnd, rightEnd]
      simpa (disch := omega) [if_pos, if_neg, ownerSite] using
        rowRedeclare_prefix F (b j.val) (b (j.val + 1))
    funext k
    have hk := k.isLt
    simp only [ownerGapStep, hrow]
    by_cases hkl : k.val = j.val
    · simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, nextBits, prefixSite, hkl]
    · by_cases hkr : k.val = j.val + 1
      · simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, nextBits, prefixSite,
          hkl, hkr, hj0]
      · rw [if_neg hkl, if_neg hkr]
        exact ownerSite_congr F g (nextGarbage F g j) b (nextBits b j) (.replyAt t) k.val
          (by simp [nextGarbage, hkl]) (by simp [nextBits, hkl, hkr])
  · have haft : t < j.val := by omega
    have hu : ownerConfigOf F g b (.replyAt t) (leftEnd F j) = .plain (.interior .empty) := by
      dsimp +instances only [ownerConfigOf, leftEnd]
      simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, leftEnd]
    have hv : ownerConfigOf F g b (.replyAt t) (rightEnd F j) =
        if j.val + 1 = F.h then .plain (.root F.d F.cw0 (resCcw F.c F.d))
        else .plain (.interior .empty) := by
      dsimp +instances only [ownerConfigOf, rightEnd]
      by_cases hl : j.val + 1 = F.h <;>
        simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, rightEnd, siteOf, hl]
    funext k
    have hk := k.isLt
    simp only [ownerGapStep, hu, hv]
    by_cases hkl : k.val = j.val
    · by_cases hl : j.val + 1 = F.h <;>
        simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, hkl, hl, rowRedeclare]
    · by_cases hkr : k.val = j.val + 1
      · by_cases hl : j.val + 1 = F.h <;>
          simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, siteOf, hkl, hkr, hl, rowRedeclare]
      · rw [if_neg hkl, if_neg hkr]
        exact ownerSite_congr F g (nextGarbage F g j) b (nextBits b j) (.replyAt t) k.val
          (by simp [nextGarbage, hkl]) (by simp [nextBits, hkl, hkr])

private theorem ownerStep_reply_no_inner (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) (hjprev : ¬ (j.val + 1 = t)) (hj0 : j.val ≠ 0) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  by_cases hjt : j.val = t
  · exact ownerStep_reply_no_inner_back F g b t ht0 hth j hjprev hj0 hjt
  · exact ownerStep_reply_no_inner_other F g b t ht0 hth j hjprev hj0 hjt

private theorem ownerStep_reply (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (t : Nat)
    (ht0 : 1 ≤ t) (hth : t < F.h) (j : Fin F.h) :
    ownerGapStep F (ownerConfigOf F g b (.replyAt t)) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F (.replyAt t) j) := by
  by_cases hjprev : j.val + 1 = t <;> by_cases hj0 : j.val = 0
  · exact ownerStep_reply_yes_root F g b t ht0 hth j hjprev hj0
  · exact ownerStep_reply_yes_inner F g b t ht0 hth j hjprev hj0
  · exact ownerStep_reply_no_root F g b t ht0 hth j hjprev hj0
  · exact ownerStep_reply_no_inner F g b t ht0 hth j hjprev hj0


private theorem ownerStep_delivered (F : Frame) (g : Nat → Slot) (b : Nat → Bool) (j : Fin F.h) :
    ownerGapStep F (ownerConfigOf F g b .delivered) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F .delivered j) := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [ownerGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> try omega
  all_goals
    by_cases hk0 : k.val = 0 <;> (try omega) <;>
      by_cases hkh : k.val = F.h <;> (try omega) <;>
      by_cases hkl : k.val = j.val <;> (try omega) <;>
      by_cases hkr : k.val = j.val + 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, nextPhase, ownerSite, ownerPort, siteOf, nextBits, prefixSite, hj0, hjh, hk0, hkh, hkl, hkr]
  all_goals
    cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      cases hv : res F.c F.d <;>
      simp_all [rowRedeclare, resolveInit_of_base F.hc, resCw, resCcw, hv,
        Verdict.cw, Verdict.ccw]

/-- Exact physical-row simulation. The old phase clock remains valid even
while the uncleared suffix contains arbitrary old messages. -/
theorem ownerGapStep_configOf (F : Frame) (g : Nat → Slot) (b : Nat → Bool)
    (p : Phase) (hp : PhaseOk F p) (j : Fin F.h) :
    ownerGapStep F (ownerConfigOf F g b p) j =
      ownerConfigOf F (nextGarbage F g j) (nextBits b j) (nextPhase F p j) := by
  cases p with
  | prelaunch => exact ownerStep_prelaunch F g b j
  | declAt t => exact ownerStep_decl F g b t hp.1 hp.2 j
  | replyAt t => exact ownerStep_reply F g b t hp.1 hp.2 j
  | delivered => exact ownerStep_delivered F g b j


/-! The physical countdown is a finite minimum, not a chosen ghost phase. -/

private theorem foldMin_lower (xs : List Nat) (B d : Nat)
    (hB : d ≤ B) (hx : ∀ x ∈ xs, d ≤ x) : d ≤ xs.foldr Nat.min B := by
  induction xs with
  | nil => exact hB
  | cons x xs ih =>
    exact Nat.le_min.mpr ⟨hx x (by simp), ih (fun y hy => hx y (by simp [hy]))⟩

private theorem foldMin_le_default (xs : List Nat) (B : Nat) : xs.foldr Nat.min B ≤ B := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.min_le_right _ _) ih

private theorem foldMin_le_member (xs : List Nat) (B x : Nat) (hx : x ∈ xs) :
    xs.foldr Nat.min B ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with he | hm
    · subst x; exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih hm)

/-- Live heads and replies offer their remaining countdowns; raw slots offer
only the default bound. The delivered owner offers zero. Authentication is
proved separately, rather than assumed by this numeric readout. -/
def ownerRank (F : Frame) (k : Nat) (a : EraseAgent) : Nat :=
  if k = 0 then
    if (project a).cwPort = some .waiting then 2 * F.h - 1 else 0
  else if k = F.h then 2 * F.h - 1
  else match a with
    | .head _ => 2 * F.h - 1 - k
    | .back _ => k
    | _ => 2 * F.h - 1

/-- Minimum raw-configuration debt: the leading head or unique reply attains
this value even when arbitrary duplicates have been injected behind it. -/
def ownerDebt (F : Frame) (cfg : EraseConfig F) : Nat :=
  (List.ofFn (fun k : Fin (F.h + 1) => ownerRank F k.val (cfg k))).foldr
    Nat.min (2 * F.h - 1)

private theorem phaseDebt_le_start (F : Frame) (p : Phase) (hp : PhaseOk F p) :
    phaseDebt F p ≤ 2 * F.h - 1 := by
  have hh := F.hpos
  cases p <;> simp only [phaseDebt, PhaseOk] at * <;> omega

private theorem ownerRank_config_lower (F : Frame) (g : Nat → Slot) (b : Nat → Bool)
    (p : Phase) (hp : PhaseOk F p) (k : Fin (F.h + 1)) :
    phaseDebt F p ≤ ownerRank F k.val (ownerConfigOf F g b p k) := by
  have hh := F.hpos
  have hk := k.isLt
  by_cases hk0 : k.val = 0 <;> by_cases hkh : k.val = F.h <;> try omega
  all_goals cases p with
  | prelaunch =>
    simp (disch := omega) [if_neg, phaseDebt, ownerRank, ownerConfigOf,
      ownerSite, ownerPort, siteOf, project, Agent.cwPort, hk0, hkh]
  | delivered => simp [phaseDebt]
  | declAt t =>
    have ht0 := hp.1
    have hth := hp.2
    by_cases hkt : k.val = t <;> by_cases hafter : t < k.val <;>
      cases hb : b k.val <;>
      simp (disch := omega) [if_pos, if_neg, phaseDebt, ownerRank, ownerConfigOf,
        ownerSite, ownerPort, siteOf, prefixSite, project, Agent.cwPort, hk0, hkh,
        hkt, hafter, hb] <;> omega
  | replyAt t =>
    have ht0 := hp.1
    have hth := hp.2
    by_cases hkt : k.val = t <;> by_cases hafter : t < k.val <;>
      cases hb : b k.val <;>
      simp (disch := omega) [if_pos, if_neg, phaseDebt, ownerRank, ownerConfigOf,
        ownerSite, ownerPort, siteOf, prefixSite, project, Agent.cwPort, hk0, hkh,
        hkt, hafter, hb] <;> omega

private theorem ownerDebt_le_rank (F : Frame) (cfg : EraseConfig F) (k : Fin (F.h + 1)) :
    ownerDebt F cfg ≤ ownerRank F k.val (cfg k) :=
  foldMin_le_member _ _ _ (List.mem_ofFn.mpr ⟨k, rfl⟩)

/-- Physical minimum readback, with no assumption that live heads are unique. -/
theorem ownerDebt_configOf (F : Frame) (g : Nat → Slot) (b : Nat → Bool)
    (p : Phase) (hp : PhaseOk F p) :
    ownerDebt F (ownerConfigOf F g b p) = phaseDebt F p := by
  apply Nat.le_antisymm
  · have hh := F.hpos
    cases p with
    | prelaunch => exact foldMin_le_default _ _
    | delivered =>
      have he := ownerDebt_le_rank F (ownerConfigOf F g b .delivered) (leftPos F)
      simpa [ownerRank, ownerConfigOf, ownerSite, ownerPort, leftPos, project,
        Agent.cwPort, resCw_ne_waiting, phaseDebt] using he
    | declAt t =>
      have ht0 := hp.1
      have hth := hp.2
      have he := ownerDebt_le_rank F (ownerConfigOf F g b (.declAt t))
        ⟨t, Nat.lt_succ_of_lt hth⟩
      simpa (disch := omega) [if_neg, ownerRank, ownerConfigOf, ownerSite, phaseDebt] using he
    | replyAt t =>
      have ht0 := hp.1
      have hth := hp.2
      have he := ownerDebt_le_rank F (ownerConfigOf F g b (.replyAt t))
        ⟨t, Nat.lt_succ_of_lt hth⟩
      simpa (disch := omega) [if_neg, ownerRank, ownerConfigOf, ownerSite, phaseDebt] using he
  · apply foldMin_lower _ _ _ (phaseDebt_le_start F p hp)
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact ownerRank_config_lower F g b p hp k



/-- Physical closure with duplicate heads included. -/
theorem ownerLane_gapStep (F : Frame) (cfg : EraseConfig F)
    (hl : OwnerLane F cfg) (j : Fin F.h) : OwnerLane F (ownerGapStep F cfg j) := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  exact ⟨nextPhase F p j, nextGarbage F g j, nextBits b j,
    nextPhase_phaseOk F p hp j, ownerGapStep_configOf F g b p hp j⟩

open Classical in
/-- Lift physical edges into the scheduler; outside edges stutter. -/
noncomputable def ownerSchedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (e : Fin n) : EraseConfig F :=
  if hx : ∃ j : Fin F.h, E.edgeAt j = e then ownerGapStep F cfg hx.choose else cfg

theorem ownerSchedStep_eq {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (j : Fin F.h) :
    ownerSchedStep F E cfg (E.edgeAt j) = ownerGapStep F cfg j := by
  classical
  have hx : ∃ a, E.edgeAt a = E.edgeAt j := ⟨j, rfl⟩
  rw [ownerSchedStep, dif_pos hx, E.inj _ _ hx.choose_spec]

theorem ownerLane_schedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (e : Fin n) :
    OwnerLane F (ownerSchedStep F E cfg e) := by
  classical
  unfold ownerSchedStep
  split
  · exact ownerLane_gapStep F cfg hl _
  · exact hl

private theorem ownerDebt_sched_config {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (g : Nat → Slot) (b : Nat → Bool) (p : Phase) (hp : PhaseOk F p) (e : Fin n) :
    ownerDebt F (ownerSchedStep F E (ownerConfigOf F g b p) e) =
      deltaOf F (schedStep F E (configOf F p) e) := by
  classical
  unfold ownerSchedStep schedStep
  split
  · rw [ownerGapStep_configOf F g b p hp,
      ownerDebt_configOf F _ _ _ (nextPhase_phaseOk F p hp _),
      gapStep_configOf F p hp, deltaOf_configOf F _ (nextPhase_phaseOk F p hp _)]
  · rw [ownerDebt_configOf F g b p hp, deltaOf_configOf F p hp]

/-- Every edge, including every re-injection/collision edge, is nonincreasing
for the physical minimum debt. -/
theorem ownerDebt_step_le {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (e : Fin n) :
    ownerDebt F (ownerSchedStep F E cfg e) ≤ ownerDebt F cfg := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  rw [ownerDebt_sched_config F E g b p hp, ownerDebt_configOf F g b p hp,
    ← deltaOf_configOf F p hp]
  exact delta_step_le F E _ (Clean.of_phaseOk F p hp) e

/-- Some physical edge lowers the debt by exactly one in every active state. -/
theorem ownerDebt_useful {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (hpos : 0 < ownerDebt F cfg) :
    ∃ a : Fin F.h, ownerDebt F (ownerSchedStep F E cfg (E.edgeAt a)) + 1 = ownerDebt F cfg := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  have hd : ownerDebt F (ownerConfigOf F g b p) = deltaOf F (configOf F p) := by
    rw [ownerDebt_configOf F g b p hp, deltaOf_configOf F p hp]
  obtain ⟨a, ha⟩ := delta_useful_lt F E _ (Clean.of_phaseOk F p hp) (by simpa [hd] using hpos)
  exact ⟨a, by simpa only [ownerDebt_sched_config F E g b p hp, hd] using ha⟩

/-- The original phase clock gives the exact scale-one child-sum inequality. -/
theorem ownerDebt_childSum {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (hpos : 0 < ownerDebt F cfg) :
    1 + (List.ofFn (fun e : Fin n => ownerDebt F (ownerSchedStep F E cfg e))).sum
      ≤ n * ownerDebt F cfg := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  have hd : ownerDebt F (ownerConfigOf F g b p) = deltaOf F (configOf F p) := by
    rw [ownerDebt_configOf F g b p hp, deltaOf_configOf F p hp]
  have h := delta_childSum F E _ (Clean.of_phaseOk F p hp) (by simpa [hd] using hpos)
  simpa only [ownerDebt_sched_config F E g b p hp, hd] using h

/-- Every permitted entry, with arbitrary unmarked residue, is represented. -/
theorem ownerStuck_representation (F : Frame) (cfg : Config F) (hi : OwnerStuck F cfg) :
    embedResidue F cfg = ownerConfigOf F (garbageOf F cfg) (fun _ => false) .prelaunch := by
  have hh := F.hpos
  funext k
  have hk := k.isLt
  by_cases hk0 : k.val = 0
  · have he : k = leftPos F := Fin.ext hk0
    subst k
    change EraseAgent.plain (cfg (leftPos F)) = .plain (.root F.c .waiting F.ccw0)
    exact congrArg EraseAgent.plain hi.1
  · by_cases hkh : k.val = F.h
    · have he : k = rightPos F := Fin.ext hkh
      subst k
      change EraseAgent.plain (cfg (rightPos F)) = ownerSite F (garbageOf F cfg) (fun _ => false) .prelaunch F.h
      rw [hi.2.1]
      simp (disch := omega) [if_neg, ownerSite, ownerPort, siteOf]
    · obtain ⟨s, hs⟩ := hi.2.2 k (by omega) (by omega)
      simp [embedResidue, ownerConfigOf, ownerSite, hk0, hkh, garbageOf, hk, hs]

theorem ownerStuck_lane (F : Frame) (cfg : Config F) (hi : OwnerStuck F cfg) :
    OwnerLane F (embedResidue F cfg) :=
  ⟨.prelaunch, garbageOf F cfg, (fun _ => false), trivial, ownerStuck_representation F cfg hi⟩

theorem ownerDebt_start (F : Frame) (cfg : Config F) (hi : OwnerStuck F cfg) :
    ownerDebt F (embedResidue F cfg) = 2 * F.h - 1 := by
  rw [ownerStuck_representation F cfg hi, ownerDebt_configOf F _ _ .prelaunch trivial]
  rfl

/-- No duplicate survives success: zero debt forces the delivered phase with
both correct receipts and completely empty interior slots. -/
theorem ownerDebt_zero_delivered (F : Frame) (cfg : EraseConfig F)
    (hl : OwnerLane F cfg) (hz : ownerDebt F cfg = 0) :
    (fun k => project (cfg k)) = configOf F .delivered := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  rw [ownerDebt_configOf F g b p hp] at hz
  have hh := F.hpos
  have hphase : p = .delivered := by
    cases p <;> simp only [PhaseOk, phaseDebt] at * <;> first | rfl | omega
  subst p
  funext k
  by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h <;>
    simp (disch := omega) [if_neg, ownerConfigOf, ownerSite, ownerPort, configOf,
      siteOf, project, h0, hlast]

/-- Active physical configurations, with no ghost state in the potential. -/
def ActiveOwner (F : Frame) := {cfg : EraseConfig F // OwnerLane F cfg ∧ 0 < ownerDebt F cfg}

noncomputable def ownerNode {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveOwner F) (e : Fin n) : StopNode (ActiveOwner F) :=
  if hp : 0 < ownerDebt F (ownerSchedStep F E s.1 e) then
    .active ⟨ownerSchedStep F E s.1 e, ownerLane_schedStep F E s.1 s.2.1 e, hp⟩
  else .success

/-- The exact interaction-scale potential is `n * ownerDebt`. -/
def ownerPotential {n : Nat} (F : Frame) : StopNode (ActiveOwner F) → Nat
  | .active s => n * ownerDebt F s.1
  | _ => 0

private theorem ownerPotential_node {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveOwner F) (e : Fin n) :
    ownerPotential (n := n) F (ownerNode F E s e) = n * ownerDebt F (ownerSchedStep F E s.1 e) := by
  unfold ownerNode
  split
  · rfl
  · rename_i hz
    have hd : ownerDebt F (ownerSchedStep F E s.1 e) = 0 := by omega
    simp [ownerPotential, hd]

/-- Scale-one Bellman certificate for the actual re-declaration table,
including all duplicate injection and collision branches. -/
theorem owner_natBellmanSuperSolution {n : Nat} (F : Frame) (E : GapEmbedding F n) :
    NatBellmanSuperSolution (ownerNode F E) 1 (ownerPotential (n := n) F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have h := Nat.mul_le_mul_left n (ownerDebt_childSum F E s.1 s.2.1 s.2.2)
  have he : (List.ofFn (fun e : Fin n => ownerPotential (n := n) F (ownerNode F E s e))).sum =
      n * (List.ofFn (fun e : Fin n => ownerDebt F (ownerSchedStep F E s.1 e))).sum := by
    rw [← ofFn_sum_mul_left]
    exact ofFn_sum_eq _ _ (fun e => ownerPotential_node F E s e)
  rw [he]
  simpa only [Nat.mul_add, Nat.mul_one, Nat.one_mul, ownerPotential] using h



/-! Authentication and an actual count of comparison-row firings. -/

/-- This records the two verdict-writing clauses of `rowRedeclare`. -/
def rowCompares : EraseAgent → EraseAgent → Nat
  | .head _, .plain (.root _ _ .free) => 1
  | .plain (.root _ .waiting _), .plain (.root _ _ .free) => 1
  | _, _ => 0

/-- A physical readout of whether the right root has already compared. -/
def comparisonMark (F : Frame) (cfg : EraseConfig F) : Nat :=
  if (project (cfg (rightPos F))).ccwPort = some .free then 0 else 1

def phaseMark : Phase → Nat
  | .prelaunch => 0
  | .declAt _ => 0
  | _ => 1

theorem comparisonMark_configOf (F : Frame) (g : Nat → Slot) (b : Nat → Bool)
    (p : Phase) : comparisonMark F (ownerConfigOf F g b p) = phaseMark p := by
  have hh := F.hpos
  cases p <;>
    simp (disch := omega) [if_neg, comparisonMark, ownerConfigOf, ownerSite,
      ownerPort, siteOf, rightPos, project, Agent.ccwPort, phaseMark, resCcw_ne_free]

/-- Count the actual comparison rows, not merely a change of a ghost flag.
No duplicate head can reach the right root after the unique reply is created. -/
theorem rowCompares_configOf (F : Frame) (g : Nat → Slot) (b : Nat → Bool)
    (p : Phase) (hp : PhaseOk F p) (j : Fin F.h) :
    rowCompares (ownerConfigOf F g b p (leftEnd F j))
        (ownerConfigOf F g b p (rightEnd F j)) + phaseMark p =
      phaseMark (nextPhase F p j) := by
  have hh := F.hpos
  have hj := j.isLt
  dsimp +instances only [ownerConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> (try omega) <;>
    by_cases hjh : j.val + 1 = F.h <;> try omega
  all_goals cases p with
  | prelaunch =>
    by_cases hh1 : F.h = 1 <;>
      simp (disch := omega) [if_pos, if_neg, ownerSite, ownerPort, siteOf,
        nextPhase, phaseMark, hj0, hjh, hh1, rowCompares]
  | declAt t =>
    have ht0 := hp.1
    have hth := hp.2
    by_cases hjt : j.val = t <;> (try omega) <;>
      by_cases hnext : j.val + 1 = t <;> (try omega) <;>
      by_cases hlast : t + 1 = F.h <;> (try omega) <;>
      by_cases hafter : t < j.val <;> try omega
    all_goals
      simp (disch := omega) [if_pos, if_neg, ownerSite, ownerPort, siteOf,
        nextPhase, phaseMark, hj0, hjh, hjt, hnext, hlast, hafter]
    all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      simp_all [prefixSite, rowCompares]
  | replyAt t =>
    have ht0 := hp.1
    have hth := hp.2
    by_cases hjt : j.val = t <;> (try omega) <;>
      by_cases hnext : j.val + 1 = t <;> (try omega) <;>
      by_cases ht1 : t = 1 <;> (try omega) <;>
      by_cases hafter : t < j.val <;> try omega
    all_goals
      simp (disch := omega) [if_pos, if_neg, ownerSite, ownerPort, siteOf,
        nextPhase, phaseMark, hj0, hjh, hjt, hnext, ht1, hafter]
    all_goals cases hb : b j.val <;> cases hb1 : b (j.val + 1) <;>
      cases hv : res F.c F.d <;>
      simp_all [prefixSite, rowCompares, resCcw, hv, Verdict.ccw]
  | delivered =>
    simp (disch := omega) [if_pos, if_neg, ownerSite, ownerPort, siteOf,
      nextPhase, phaseMark, hj0, hjh]
    all_goals cases hv : res F.c F.d <;>
      simp [rowCompares, resCw, resCcw, hv, Verdict.cw, Verdict.ccw]

open Classical in
/-- One scheduler edge's actual comparison count (zero for outside edges). -/
noncomputable def comparisonEvent {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (e : Fin n) : Nat :=
  if hx : ∃ j : Fin F.h, E.edgeAt j = e then
    rowCompares (cfg (leftEnd F hx.choose)) (cfg (rightEnd F hx.choose))
  else 0

/-- A comparison consumes the free right port. It can never be counted twice. -/
theorem comparisonEvent_balance {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (e : Fin n) :
    comparisonEvent F E cfg e + comparisonMark F cfg =
      comparisonMark F (ownerSchedStep F E cfg e) := by
  classical
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  unfold comparisonEvent ownerSchedStep
  split
  · rw [ownerGapStep_configOf F g b p hp,
      comparisonMark_configOf, comparisonMark_configOf]
    exact rowCompares_configOf F g b p hp _
  · simp [comparisonMark_configOf]

/-- Correct ports and payloads at every state in the duplicate-aware lane. -/
theorem ownerLane_authentic (F : Frame) (cfg : EraseConfig F) (hl : OwnerLane F cfg) :
    ((project (cfg (rightPos F))).ccwPort = some .free ∨
      (project (cfg (rightPos F))).ccwPort = some (resCcw F.c F.d)) ∧
    ((project (cfg (leftPos F))).cwPort = some .waiting ∨
      (project (cfg (leftPos F))).cwPort = some (resCw F.c F.d)) ∧
    (∀ k c0, cfg k = .head c0 → c0 = F.c) ∧
    (∀ k d0, cfg k = .back d0 → d0 = F.d) := by
  obtain ⟨p, g, b, hp, rfl⟩ := hl
  have hh := F.hpos
  constructor
  · cases p <;>
      simp (disch := omega) [if_neg, ownerConfigOf, ownerSite, ownerPort,
        siteOf, rightPos, project, Agent.ccwPort]
  · constructor
    · cases p <;> simp [ownerConfigOf, ownerSite, ownerPort, leftPos, project, Agent.cwPort]
    · constructor
      · intro k c0 he
        by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
        all_goals cases p with
        | prelaunch => simp_all [ownerConfigOf, ownerSite]
        | delivered => simp_all [ownerConfigOf, ownerSite]
        | declAt t =>
          by_cases ht : k.val = t <;> by_cases ha : t < k.val <;> cases hb : b k.val <;>
            simp_all [ownerConfigOf, ownerSite, prefixSite]
        | replyAt t =>
          by_cases ht : k.val = t <;> by_cases ha : t < k.val <;> cases hb : b k.val <;>
            simp_all [ownerConfigOf, ownerSite, prefixSite]
      · intro k d0 he
        by_cases h0 : k.val = 0 <;> by_cases hlast : k.val = F.h
        all_goals cases p with
        | prelaunch => simp_all [ownerConfigOf, ownerSite]
        | delivered => simp_all [ownerConfigOf, ownerSite]
        | declAt t =>
          by_cases ht : k.val = t <;> by_cases ha : t < k.val <;> cases hb : b k.val <;>
            simp_all [ownerConfigOf, ownerSite, prefixSite]
        | replyAt t =>
          by_cases ht : k.val = t <;> by_cases ha : t < k.val <;> cases hb : b k.val <;>
            simp_all [ownerConfigOf, ownerSite, prefixSite]

/-- Finite execution under the repaired physical scheduler. -/
noncomputable def ownerRun {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) : List (Fin n) → EraseConfig F
  | [] => cfg
  | e :: es => ownerRun F E (ownerSchedStep F E cfg e) es

/-- Number of actual verdict-writing row firings along a schedule. -/
noncomputable def comparisonCount {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) : List (Fin n) → Nat
  | [] => 0
  | e :: es => comparisonEvent F E cfg e + comparisonCount F E (ownerSchedStep F E cfg e) es

theorem ownerLane_run {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (es : List (Fin n)) :
    OwnerLane F (ownerRun F E cfg es) := by
  induction es generalizing cfg with
  | nil => exact hl
  | cons e es ih => exact ih _ (ownerLane_schedStep F E cfg hl e)

/-- Telescoping counts all real comparisons, independently of duplicate count. -/
theorem comparisonCount_balance {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : EraseConfig F) (hl : OwnerLane F cfg) (es : List (Fin n)) :
    comparisonCount F E cfg es + comparisonMark F cfg = comparisonMark F (ownerRun F E cfg es) := by
  induction es generalizing cfg with
  | nil => simp [comparisonCount, ownerRun]
  | cons e es ih =>
    have h1 := comparisonEvent_balance F E cfg hl e
    have h2 := ih _ (ownerLane_schedStep F E cfg hl e)
    simp only [comparisonCount, ownerRun]
    omega

/-- Stronger than at-most-once per live declaration: the right root compares
at most once in the entire service, however many duplicate declarations are
injected. Both visible receipts and all live payloads are correct. -/
theorem duplicate_safe {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : OwnerStuck F cfg) (es : List (Fin n)) :
    let out := ownerRun F E (embedResidue F cfg) es
    comparisonCount F E (embedResidue F cfg) es ≤ 1 ∧
    ((project (out (rightPos F))).ccwPort = some .free ∨
      (project (out (rightPos F))).ccwPort = some (resCcw F.c F.d)) ∧
    ((project (out (leftPos F))).cwPort = some .waiting ∨
      (project (out (leftPos F))).cwPort = some (resCw F.c F.d)) ∧
    (∀ k c0, out k = .head c0 → c0 = F.c) ∧
    (∀ k d0, out k = .back d0 → d0 = F.d) := by
  constructor
  · have h := comparisonCount_balance F E _ (ownerStuck_lane F cfg hi) es
    have hm : comparisonMark F (ownerRun F E (embedResidue F cfg) es) ≤ 1 := by
      unfold comparisonMark
      split <;> omega
    omega
  · exact ownerLane_authentic F _ (ownerLane_run F E _ (ownerStuck_lane F cfg hi) es)



/-! Collision witnesses and end-to-end convergence. -/

/-- The reply survives a head-on collision and moves toward its owner. -/
theorem reply_wins_collision (c d : Choice) :
    rowRedeclare (.head c) (.back d) = (.back d, .plain (.interior .empty)) := rfl

/-- Coalescing declarations keeps the forward head and deletes the rear one. -/
theorem duplicate_heads_coalesce (c c' : Choice) :
    rowRedeclare (.head c) (.head c') = (.plain (.interior .empty), .head c') := rfl

/-- A token deeper in the gap is invisible to the first-slot guard: this is
an explicit general-length configuration where re-injection creates two heads. -/
theorem first_slot_guard_insufficient (F : Frame) (hh : 2 < F.h) :
    let cfg := ownerConfigOf F (fun _ => .empty) (fun _ => false) (.declAt 2)
    cfg ⟨1, by omega⟩ = .plain (.interior .empty) ∧
    cfg ⟨2, by omega⟩ = .head F.c ∧
    ownerGapStep F cfg ⟨0, F.hpos⟩ ⟨1, by omega⟩ = .head F.c ∧
    ownerGapStep F cfg ⟨0, F.hpos⟩ ⟨2, by omega⟩ = .head F.c := by
  simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, ownerPort,
    prefixSite, ownerGapStep, leftEnd, rightEnd, rowRedeclare, resolveInit_of_base F.hc]

/-- The same hidden-token situation with a returning reply is safe: injection
creates a head immediately to its left, and the collision moves that reply
left while clearing its former slot. -/
theorem returning_reply_collision (F : Frame) (hh : 2 < F.h) :
    let cfg := ownerConfigOf F (fun _ => .empty) (fun _ => false) (.replyAt 2)
    let injected := ownerGapStep F cfg ⟨0, F.hpos⟩
    let collided := ownerGapStep F injected ⟨1, by omega⟩
    injected ⟨1, by omega⟩ = .head F.c ∧
    injected ⟨2, by omega⟩ = .back F.d ∧
    collided ⟨1, by omega⟩ = .back F.d ∧
    collided ⟨2, by omega⟩ = .plain (.interior .empty) := by
  simp (disch := omega) [if_pos, if_neg, ownerConfigOf, ownerSite, ownerPort,
    prefixSite, ownerGapStep, leftEnd, rightEnd, rowRedeclare, resolveInit_of_base F.hc]

/-- A waiting owner over an empty gap is indeed fixed under the old erasure
table, for every physical gap edge including the one-edge root/root case. -/
theorem old_waiting_empty_fixed (F : Frame) (j : Fin F.h) :
    let cfg := ownerConfigOf F (fun _ => .empty) (fun _ => false) .prelaunch
    eraseGapStep F cfg j = cfg := by
  have hh := F.hpos
  have hj := j.isLt
  funext k
  have hk := k.isLt
  dsimp +instances only [eraseGapStep, ownerConfigOf, leftEnd, rightEnd]
  by_cases hj0 : j.val = 0 <;> by_cases hjh : j.val + 1 = F.h
  all_goals
    by_cases hk0 : k.val = 0 <;> by_cases hkh : k.val = F.h <;>
      by_cases hkl : k.val = j.val <;> by_cases hkr : k.val = j.val + 1 <;> try omega
  all_goals
    simp (disch := omega) [if_pos, if_neg, ownerSite, ownerPort, siteOf,
      hj0, hjh, hk0, hkh, hkl, hkr, rowErase]

/-- The repair starts without any missing positivity premise. -/
def ownerStart (F : Frame) (cfg : Config F) (hi : OwnerStuck F cfg) : ActiveOwner F :=
  ⟨embedResidue F cfg, ownerStuck_lane F cfg hi, by
    rw [ownerDebt_start F cfg hi]
    have hh := F.hpos
    omega⟩

/-- Exact start budget for every allowed waiting-owner residue. -/
theorem ownerPotential_start {n : Nat} (F : Frame) (cfg : Config F) (hi : OwnerStuck F cfg) :
    ownerPotential (n := n) F (.active (ownerStart F cfg hi)) = n * (2 * F.h - 1) := by
  change n * ownerDebt F (embedResidue F cfg) = _
  rw [ownerDebt_start F cfg hi]

theorem ownerNode_ne_failure {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveOwner F) (e : Fin n) : ownerNode F E s e ≠ .failure := by
  unfold ownerNode
  split <;> simp

/-- Every successful stopping edge really delivers, with no hidden duplicates. -/
theorem owner_success_delivered {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (s : ActiveOwner F) (e : Fin n) (hs : ownerNode F E s e = .success) :
    (fun k => project (ownerSchedStep F E s.1 e k)) = configOf F .delivered := by
  apply ownerDebt_zero_delivered F _ (ownerLane_schedStep F E s.1 s.2.1 e)
  unfold ownerNode at hs
  split at hs
  · contradiction
  · omega

/-- Uniform finite-horizon cost bound; the raw scheduler pays scale one. -/
theorem owner_residue_converges {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : OwnerStuck F cfg) (T : Nat) :
    truncatedActiveCostNumerator (ownerNode F E) (.active (ownerStart F cfg hi)) T
      ≤ n ^ T * (n * (2 * F.h - 1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (ownerNode F E) 1 (ownerPotential (n := n) F)
    (owner_natBellmanSuperSolution F E) (.active (ownerStart F cfg hi)) T
  simpa only [Nat.one_mul, ownerPotential_start] using h

/-- Division-free reciprocal bound on unfinished scheduler mass. -/
theorem owner_residue_tail {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : OwnerStuck F cfg) (T : Nat) :
    T * activeCount (ownerNode F E) (.active (ownerStart F cfg hi)) T
      ≤ n ^ T * (n * (2 * F.h - 1)) :=
  Nat.le_trans (horizon_mul_activeCount_le_truncatedActiveCostNumerator
    (ownerNode F E) (.active (ownerStart F cfg hi)) T)
    (owner_residue_converges F E cfg hi T)

private theorem owner_reaches_in {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (D : Nat) : ∀ cfg : EraseConfig F, OwnerLane F cfg → ownerDebt F cfg ≤ D →
    ∃ es : List (Fin n), es.length ≤ D ∧
      (fun k => project (ownerRun F E cfg es k)) = configOf F .delivered := by
  induction D with
  | zero =>
    intro cfg hl hd
    exact ⟨[], Nat.le_refl 0, ownerDebt_zero_delivered F cfg hl (by omega)⟩
  | succ D ih =>
    intro cfg hl hd
    by_cases hz : ownerDebt F cfg = 0
    · exact ⟨[], Nat.zero_le _, ownerDebt_zero_delivered F cfg hl hz⟩
    · obtain ⟨a, ha⟩ := ownerDebt_useful F E cfg hl (by omega)
      obtain ⟨es, hlen, hend⟩ := ih (ownerSchedStep F E cfg (E.edgeAt a))
        (ownerLane_schedStep F E cfg hl _) (by omega)
      exact ⟨E.edgeAt a :: es, by simp only [List.length_cons]; omega, hend⟩

/-- Constructive reachability of the original delivered clean configuration,
separate from the bound on random-scheduler stutters. -/
theorem owner_reaches_clean {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : Config F) (hi : OwnerStuck F cfg) :
    ∃ es : List (Fin n), es.length ≤ 2 * F.h - 1 ∧
      (fun k => project (ownerRun F E (embedResidue F cfg) es k)) = configOf F .delivered ∧
      Clean F (fun k => project (ownerRun F E (embedResidue F cfg) es k)) := by
  obtain ⟨es, hlen, hend⟩ := owner_reaches_in F E (2 * F.h - 1)
    (embedResidue F cfg) (ownerStuck_lane F cfg hi) (Nat.le_of_eq (ownerDebt_start F cfg hi))
  exact ⟨es, hlen, hend, hend ▸ Clean.delivered⟩

#print axioms duplicate_safe
#print axioms owner_natBellmanSuperSolution
#print axioms owner_residue_converges
#print axioms owner_reaches_clean

end ShortGapLiteralOwnerResidue
