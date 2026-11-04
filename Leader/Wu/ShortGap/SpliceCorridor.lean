import Leader.Wu.ShortGap.SpliceCommit

namespace ShortGapSpliceCorridor

open ShortGapLiteralGapRows ShortGapCaptureReservation ShortGapCaptureCommitRows
open ShortGapSpliceCommit
open FiniteUniformStoppingTree

set_option autoImplicit false

/-!
# The splice corridor: the literal retirement tail of one commit

New file: `Leader/Wu/ShortGap/SpliceCorridor.lean`.

`Leader/Wu/ShortGap/SpliceCommit.lean` supplies the local splice table
(`spliceRow` / `spliceRule` on `SNode` pairs) and an *abstract* tail machine
`TailPhase x` with `spliceTailStep`, `splice_bellman` and `spliceDebt x = x+1`.
Its open item was that no row/phase simulation existed on a literal corridor
configuration.  This file supplies exactly that corridor and the simulation.

The corridor is the physical interval left behind by one commit at `B`:

* offset `0`   -- `A`, the source root, already `adopted` (the COMMITTED
  receipt has been deposited, `A.cw := adopt(snapshot)`);
* offsets `1 .. x-1` -- the `x-1` former `(A,B)` capture cells, now empty;
* offset `x`   -- former `B`, no longer a leader, carrying the stationary
  `bridge` snapshot; its clockwise port still holds the settled old `(B,C)`
  verdict, and the whole `(B,C)` side lives beyond offset `x`.

Everything proved here is local: literal pair firings on this interval, an
exact simulation against the tail machine, the frame of the `(B,C)` side, and
the transported cost bound.  No freshness, reachability or fairness statement
is made.
-/

/-! ## The corridor frame -/

/-- Static data of one splice corridor.  `x` is the physical length of the
former `(A,B)` capture corridor; `x ≥ 2` because the length-one corridor has
no interior cell at all (see `corridor_length_one_stalls`).

`aCw ≠ .heldCandidate` is not an assumption about the protocol: `A.cw` is
written by the adopt row as `adoptCwOf`, and `adoptCwOf_ne_candidate` (imported)
shows that value is never `heldCandidate`. -/
structure SFrame where
  x : Nat
  hx : 2 ≤ x
  aCw : CwPort
  haCw : aCw ≠ .heldCandidate
  aCcw : CcwPort
  aInc : InControl
  aCtl : CommitCtl
  aLease : CommitIn
  bCw : CwPort
  hbCw : bCw = .heldDenial ∨ bCw = .heldCandidate
  bOut : OutControl
  bCtl : CommitCtl
  bSnap : SnapPhase

/-- Every frame produced by an actual adopt row satisfies `haCw`. -/
theorem aCw_ne_candidate_of_adopt (s : Option SnapPhase) :
    adoptCwOf s ≠ .heldCandidate := adoptCwOf_ne_candidate s

/-- `A`'s raw node: the FINAL-ready source root of the retired episode. -/
def aRaw (F : SFrame) : Node := .root .out1 F.aCw F.aCcw .finalReady F.aInc

/-- Former `B`'s raw node.  Its `cw` port is the settled old `(B,C)` verdict;
that port and everything past offset `x` is the `(B,C)` side. -/
def bridgeRaw (F : SFrame) : Node := .root .in0 F.bCw .heldCandidate F.bOut .accepted

/-- `A` at offset `0`, in splice lifecycle state `sp`. -/
def aNode (F : SFrame) (sp : SpliceCtl) : SNode :=
  ⟨⟨aRaw F, false, F.aCtl, F.aLease, .none⟩, none, none, sp, .none, .none⟩

/-- One cleaned former capture cell, carrying the retirement witness `w`. -/
def cellN (w : RetireWitness) : SNode := sCell .none w .none none

/-- Former `B` at offset `x`, carrying the stationary bridge snapshot. -/
def bridgeN (F : SFrame) (sp : SpliceCtl) : SNode :=
  ⟨⟨bridgeRaw F, false, F.bCtl, .committed, .none⟩, some F.bSnap, none, sp, .none, .none⟩

theorem aNode_eq (F : SFrame) (sp : SpliceCtl) :
    aNode F sp = sRootAt F.aCw F.aCcw F.aInc F.aCtl F.aLease sp .none := rfl

theorem bridgeN_bridged_eq (F : SFrame) :
    bridgeN F .bridged = sBridge F.bCw F.bOut F.bCtl F.bSnap := rfl

theorem settledCw_bridgeRaw (F : SFrame) : settledCw (bridgeRaw F) = true := by
  rcases F.hbCw with h | h <;> (unfold bridgeRaw settledCw; rw [h])

theorem decodeLeft_aRaw (F : SFrame) : decodeLeft (aRaw F) = none := by
  unfold aRaw
  cases h : F.aCw
  · rfl
  · rfl
  · rfl
  · exact absurd h F.haCw


/-! ## Dispatch helpers -/

private theorem rawOwner_root_out1 (cw : CwPort) (ccw : CcwPort) (inc : InControl)
    (h : cw ≠ .heldCandidate) :
    rawOwner (Node.root .out1 cw ccw .finalReady inc) = false := by
  cases cw
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h

theorem rawOwner_aRaw (F : SFrame) : rawOwner (aRaw F) = false :=
  rawOwner_root_out1 F.aCw F.aCcw F.aInc F.haCw

theorem captureRow_aRaw (F : SFrame) (b : Node) : captureRow (aRaw F) b = (aRaw F, b) :=
  captureRow_of_left_none _ _ (decodeLeft_aRaw F)

/-- The `.core` fallback of the splice dispatcher. -/
theorem spliceRow_core_of (a b : SNode)
    (h1 : ¬ FreshFlush a b) (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h9 : ¬ HandoffArm a) :
    spliceRow a b = liftPair a b (commitRow a.core b.core) := by
  have hr : srun a b =
      { rule := .core (commitRule a.core b.core)
        left := (liftPair a b (commitRow a.core b.core)).1
        right := (liftPair a b (commitRow a.core b.core)).2
        valid := .core } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
      dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9]
  exact congrArg (fun r : SResult a b => (r.left, r.right)) hr

/-- The `.idle` fallback of the imported commit dispatcher. -/
theorem commitRow_idle_of (a b : CNode)
    (g1 : ¬ SourceAck a) (g2 : ¬ TargetCleanup a) (g3 : ¬ Legacy a b) (g4 : ¬ Launch a b)
    (g5 : ¬ Forward a b) (g6 : ¬ AtTarget a b) (g7 : ¬ Backward a b) (g8 : ¬ Deposit a b)
    (g9 : ¬ Direct a b) : commitRow a b = (a, b) := by
  have hr : run a b = { rule := .idle, left := a, right := b, valid := .idle } := by
    simp only [run, dif_neg g1, dif_neg g2, dif_neg g3, dif_neg g4, dif_neg g5,
      dif_neg g6, dif_neg g7, dif_neg g8, dif_neg g9]
  exact congrArg (fun r : Result a b => (r.left, r.right)) hr

/-- A pair on which neither the splice table nor the imported commit table has
an enabled row is a literal stutter of the whole wrapper. -/
theorem spliceRow_stutter_of (a b : SNode)
    (hcore : spliceRow a b = liftPair a b (commitRow a.core b.core))
    (hidle : commitRow a.core b.core = (a.core, b.core))
    (hc : committedNow b.core b.core = false)
    (hm : receiptMoved b.core a.core b.core = false) :
    spliceRow a b = (a, b) := by
  rw [hcore, hidle]
  show (liftLeft a b a.core b.core, liftRight b a.core b.core) = (a, b)
  unfold liftLeft liftRight
  rw [hc, hm]
  rfl

/-! ## The literal pair firings of the corridor

Six pair shapes occur on the corridor: three of them fire a retirement row,
three of them are literal stutters of the whole wrapper (splice table and
imported commit table together).
-/

/-- The conversion at the bridge: the settled old `(B,C)` verdict becomes a
retirement witness *and* the witness is handed to the last capture cell, in
one firing.  The bridge is spent (`bridged -> drained`); no raw field moves. -/
theorem row_convert (F : SFrame) :
    spliceRow (cellN .none) (bridgeN F .bridged) = (cellN .token, bridgeN F .drained) := by
  have h1 : ¬ FreshFlush (cellN .none) (bridgeN F .bridged) := by
    intro h; cases h.1
  have h2 : ¬ FreshLaunch (cellN .none) (bridgeN F .bridged) := by
    intro h; cases h.1
  have h3 : ¬ FreshForward (cellN .none) (bridgeN F .bridged) := by
    intro h; cases h.1
  have hg : RetireLaunch (cellN .none) (bridgeN F .bridged) :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, settledCw_bridgeRaw F, rfl⟩
  have hr : srun (cellN .none) (bridgeN F .bridged) =
      { rule := .retireLaunch, left := witnessL (cellN .none), right := drainR (bridgeN F .bridged),
        valid := .retireLaunch hg } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos hg]
  exact congrArg (fun r : SResult (cellN .none) (bridgeN F .bridged) => (r.left, r.right)) hr

/-- The witness travels one cell towards `A`. -/
theorem row_carry :
    spliceRow (cellN .none) (cellN .token) = (cellN .token, cellN .none) :=
  splice_retire_backward

/-- The witness lands at the adopted `A`, which retires.  Only the A-side
lifecycle mark is written. -/
theorem row_land (F : SFrame) :
    spliceRow (aNode F .adopted) (cellN .token) = (aNode F .retired, cellN .none) :=
  splice_retire_deposit F.aCw F.aCcw F.aInc F.aCtl F.aLease

/-- Two cleaned cells: nothing is enabled. -/
theorem row_cells (w : RetireWitness) :
    spliceRow (cellN w) (cellN .none) = (cellN w, cellN .none) := by
  cases w <;> rfl

/-- The adopted `A` and a cleaned cell: nothing is enabled. -/
theorem row_idleA (F : SFrame) :
    spliceRow (aNode F .adopted) (cellN .none) = (aNode F .adopted, cellN .none) := by
  have hown : ¬ Owner (aNode F .adopted).core := by
    intro h
    have hx : rawOwner (aRaw F) = true := h.1
    rw [rawOwner_aRaw F] at hx
    cases hx
  have hcore : spliceRow (aNode F .adopted) (cellN .none) =
      liftPair (aNode F .adopted) (cellN .none)
        (commitRow (aNode F .adopted).core (cellN .none).core) := by
    refine spliceRow_core_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1.1
    · intro h; cases h.1.1
    · intro h; cases h.2.2
    · intro h; exact h.2.1 rfl
    · intro h; exact h.2.1 rfl
    · intro h; cases h.1
  have hidle : commitRow (aNode F .adopted).core (cellN .none).core =
      ((aNode F .adopted).core, (cellN .none).core) := by
    refine commitRow_idle_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; exact hown h.1
    · intro h; cases h.1.1
    · intro h; exact h.2.2.2.2 (captureRow_aRaw F _)
    · intro h; exact hown h.1
    · intro h; cases h.1.2
    · intro h; cases h.1.2
    · intro h; cases h.1.1
    · intro h; exact hown h.1
    · intro h; exact hown h.1
  exact spliceRow_stutter_of _ _ hcore hidle rfl rfl

/-- A spent bridge: no retirement row is enabled against it any more, in
either witness state of the neighbouring cell. -/
theorem row_idleBridge (F : SFrame) (w : RetireWitness) :
    spliceRow (cellN w) (bridgeN F .drained) = (cellN w, bridgeN F .drained) := by
  have hcore : spliceRow (cellN w) (bridgeN F .drained) =
      liftPair (cellN w) (bridgeN F .drained)
        (commitRow (cellN w).core (bridgeN F .drained).core) := by
    refine spliceRow_core_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.2.2.1
    · intro h; cases h.2.2.1.1
    · intro h; cases h.1
    · intro h; exact h.2.1 rfl
    · intro h; exact h.2.1 rfl
    · intro h; cases h.1
  have hseed : seedIn (bridgeRaw F) = .reserved := rfl
  have hidle : commitRow (cellN w).core (bridgeN F .drained).core =
      ((cellN w).core, (bridgeN F .drained).core) := by
    refine commitRow_idle_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1.1
    · intro h; cases h.1.1
    · intro h
      have hx : CommitIn.committed = seedIn (bridgeRaw F) := h.2.1.2
      rw [hseed] at hx
      cases hx
    · intro h; cases h.1.1
    · intro h; cases h.1.2
    · intro h; cases h.1.2
    · intro h; cases h.2.1
    · intro h; cases h.1.1
    · intro h; cases h.1.1
  exact spliceRow_stutter_of _ _ hcore hidle rfl rfl

/-! ## The corridor as a configuration on `Fin (x+1)` -/

/-- A corridor configuration: offset `0` is `A`, offsets `1 … x-1` are the
former capture cells, offset `x` is former `B` (the bridge). -/
abbrev SpliceConfig (F : SFrame) := Fin (F.x + 1) → SNode

def leftEndS (F : SFrame) (a : Fin F.x) : Fin (F.x + 1) :=
  ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩

def rightEndS (F : SFrame) (a : Fin F.x) : Fin (F.x + 1) :=
  ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩

/-- Scheduling corridor edge `a`: apply the literal splice row to offsets
`a` and `a+1`, and update exactly those two offsets. -/
def spliceGapStep (F : SFrame) (cfg : SpliceConfig F) (a : Fin F.x) : SpliceConfig F :=
  fun k =>
    if k.val = a.val then (spliceRow (cfg (leftEndS F a)) (cfg (rightEndS F a))).1
    else if k.val = a.val + 1 then (spliceRow (cfg (leftEndS F a)) (cfg (rightEndS F a))).2
    else cfg k

theorem spliceGapStep_of (F : SFrame) (cfg cfg' : SpliceConfig F) (a : Fin F.x)
    (hrow : spliceRow (cfg (leftEndS F a)) (cfg (rightEndS F a))
      = (cfg' (leftEndS F a), cfg' (rightEndS F a)))
    (hframe : ∀ k : Fin (F.x + 1), k.val ≠ a.val → k.val ≠ a.val + 1 → cfg' k = cfg k) :
    spliceGapStep F cfg a = cfg' := by
  funext k
  unfold spliceGapStep
  by_cases h1 : k.val = a.val
  · rw [if_pos h1, hrow]
    exact congrArg cfg' (Fin.ext (show (leftEndS F a).val = k.val from h1.symm))
  · rw [if_neg h1]
    by_cases h2 : k.val = a.val + 1
    · rw [if_pos h2, hrow]
      exact congrArg cfg' (Fin.ext (show (rightEndS F a).val = k.val from h2.symm))
    · rw [if_neg h2]
      exact (hframe k h1 h2).symm

theorem spliceGapStep_id (F : SFrame) (cfg : SpliceConfig F) (a : Fin F.x)
    (hrow : spliceRow (cfg (leftEndS F a)) (cfg (rightEndS F a))
      = (cfg (leftEndS F a), cfg (rightEndS F a))) :
    spliceGapStep F cfg a = cfg :=
  spliceGapStep_of F cfg cfg a hrow (fun _ _ _ => rfl)

/-- The clean lane of the corridor: `A` in lifecycle state `asp`, the bridge
in lifecycle state `bsp`, the retirement witness at offset `tok` (`tok = 0`
means: no witness in the corridor), every other cell cleaned. -/
def corridorNode (F : SFrame) (asp bsp : SpliceCtl) (tok k : Nat) : SNode :=
  if k = 0 then aNode F asp
  else if k = F.x then bridgeN F bsp
  else if k = tok then cellN .token
  else cellN .none

def corridorCfg (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat) : SpliceConfig F :=
  fun k => corridorNode F asp bsp tok k.val

theorem corridorCfg_at_zero (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h : k.val = 0) : corridorCfg F asp bsp tok k = aNode F asp := by
  unfold corridorCfg corridorNode
  rw [if_pos h]

theorem corridorCfg_at_top (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h : k.val = F.x) : corridorCfg F asp bsp tok k = bridgeN F bsp := by
  have hx := F.hx
  unfold corridorCfg corridorNode
  rw [if_neg (by omega), if_pos h]

theorem corridorCfg_at_tok (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) (h : k.val = tok) :
    corridorCfg F asp bsp tok k = cellN .token := by
  unfold corridorCfg corridorNode
  rw [if_neg h0, if_neg hx, if_pos h]

theorem corridorCfg_at_cell (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) (h : k.val ≠ tok) :
    corridorCfg F asp bsp tok k = cellN .none := by
  unfold corridorCfg corridorNode
  rw [if_neg h0, if_neg hx, if_neg h]

theorem corridorCfg_at_any (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) :
    corridorCfg F asp bsp tok k = cellN (if k.val = tok then .token else .none) := by
  by_cases h : k.val = tok
  · rw [corridorCfg_at_tok F asp bsp tok k h0 hx h, if_pos h]
  · rw [corridorCfg_at_cell F asp bsp tok k h0 hx h, if_neg h]

/-- Off the two written offsets the whole clean lane is framed. -/
theorem corridorCfg_frame (F : SFrame) (asp asp' bsp bsp' : SpliceCtl) (tok tok' : Nat)
    (k : Fin (F.x + 1))
    (ha : k.val = 0 → asp' = asp) (hb : k.val = F.x → bsp' = bsp)
    (ht1 : k.val ≠ 0 → k.val ≠ F.x → k.val ≠ tok)
    (ht2 : k.val ≠ 0 → k.val ≠ F.x → k.val ≠ tok') :
    corridorCfg F asp' bsp' tok' k = corridorCfg F asp bsp tok k := by
  unfold corridorCfg corridorNode
  by_cases h0 : k.val = 0
  · rw [if_pos h0, if_pos h0, ha h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hx : k.val = F.x
    · rw [if_pos hx, if_pos hx, hb hx]
    · rw [if_neg hx, if_neg hx, if_neg (ht1 h0 hx), if_neg (ht2 h0 hx)]

/-! ## The five corridor firings -/

/-- The bridge edge `(x-1, x)`. -/
def convEdge (F : SFrame) : Fin F.x := ⟨F.x - 1, by have := F.hx; omega⟩

/-- The conversion firing: one firing of the bridge edge retires the bridge
*and* places the witness on the last capture cell. -/
theorem step_convert (F : SFrame) :
    spliceGapStep F (corridorCfg F .adopted .bridged 0) (convEdge F)
      = corridorCfg F .adopted .drained (F.x - 1) := by
  have hx2 := F.hx
  have hlv : (leftEndS F (convEdge F)).val = F.x - 1 := rfl
  have hrv : (rightEndS F (convEdge F)).val = F.x := by
    show F.x - 1 + 1 = F.x
    omega
  refine spliceGapStep_of F _ _ _ ?_ ?_
  · rw [corridorCfg_at_cell F .adopted .bridged 0 _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        corridorCfg_at_top F .adopted .bridged 0 _ hrv,
        corridorCfg_at_tok F .adopted .drained (F.x - 1) _ (by rw [hlv]; omega)
          (by rw [hlv]; omega) hlv,
        corridorCfg_at_top F .adopted .drained (F.x - 1) _ hrv]
    exact row_convert F
  · intro k h1 h2
    have h1' : k.val ≠ F.x - 1 := h1
    have h2' : k.val ≠ F.x - 1 + 1 := h2
    exact corridorCfg_frame F .adopted .adopted .bridged .drained 0 (F.x - 1) k
      (fun _ => rfl) (fun hk => absurd hk (by omega)) (fun h _ => h) (fun _ _ => h1')

/-- The witness travels one cell towards `A`. -/
theorem step_carry (F : SFrame) (j : Nat) (hj2 : 2 ≤ j) (hjx : j ≤ F.x - 1)
    (a : Fin F.x) (ha : a.val = j - 1) :
    spliceGapStep F (corridorCfg F .adopted .drained j) a
      = corridorCfg F .adopted .drained (j - 1) := by
  have hx2 := F.hx
  have hlv : (leftEndS F a).val = j - 1 := ha
  have hrv : (rightEndS F a).val = j := by
    show a.val + 1 = j
    omega
  refine spliceGapStep_of F _ _ _ ?_ ?_
  · rw [corridorCfg_at_cell F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        corridorCfg_at_tok F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega) hrv,
        corridorCfg_at_tok F .adopted .drained (j - 1) _ (by rw [hlv]; omega)
          (by rw [hlv]; omega) hlv,
        corridorCfg_at_cell F .adopted .drained (j - 1) _ (by rw [hrv]; omega)
          (by rw [hrv]; omega) (by rw [hrv]; omega)]
    exact row_carry
  · intro k h1 h2
    have h1' : k.val ≠ j - 1 := by rw [ha] at h1; exact h1
    have h2' : k.val ≠ j := by rw [ha] at h2; omega
    exact corridorCfg_frame F .adopted .adopted .drained .drained j (j - 1) k
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => h2') (fun _ _ => h1')

/-- The witness lands at `A`, which retires. -/
theorem step_land (F : SFrame) (a : Fin F.x) (ha : a.val = 0) :
    spliceGapStep F (corridorCfg F .adopted .drained 1) a
      = corridorCfg F .retired .drained 0 := by
  have hx2 := F.hx
  have hlv : (leftEndS F a).val = 0 := ha
  have hrv : (rightEndS F a).val = 1 := by
    show a.val + 1 = 1
    omega
  refine spliceGapStep_of F _ _ _ ?_ ?_
  · rw [corridorCfg_at_zero F .adopted .drained 1 _ hlv,
        corridorCfg_at_tok F .adopted .drained 1 _ (by rw [hrv]; omega) (by rw [hrv]; omega) hrv,
        corridorCfg_at_zero F .retired .drained 0 _ hlv,
        corridorCfg_at_cell F .retired .drained 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact row_land F
  · intro k h1 h2
    have h1' : k.val ≠ 0 := by rw [ha] at h1; exact h1
    have h2' : k.val ≠ 1 := by rw [ha] at h2; exact h2
    exact corridorCfg_frame F .adopted .retired .drained .drained 1 0 k
      (fun hk => absurd hk h1') (fun _ => rfl) (fun _ _ => h2') (fun _ _ => h1')

/-- Every other edge stutters on the pre-conversion configuration. -/
theorem step_stutter_convert (F : SFrame) (a : Fin F.x) (ha : a.val ≠ F.x - 1) :
    spliceGapStep F (corridorCfg F .adopted .bridged 0) a
      = corridorCfg F .adopted .bridged 0 := by
  have hx2 := F.hx
  have haLt := a.isLt
  have hlv : (leftEndS F a).val = a.val := rfl
  have hrv : (rightEndS F a).val = a.val + 1 := rfl
  refine spliceGapStep_id F _ _ ?_
  by_cases h0 : a.val = 0
  · rw [corridorCfg_at_zero F .adopted .bridged 0 _ (by rw [hlv]; omega),
        corridorCfg_at_cell F .adopted .bridged 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact row_idleA F
  · rw [corridorCfg_at_cell F .adopted .bridged 0 _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        corridorCfg_at_cell F .adopted .bridged 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact row_cells .none

/-- Every edge other than the witness's own edge stutters while the witness
walks. -/
theorem step_stutter_witness (F : SFrame) (j : Nat)
    (a : Fin F.x) (ha : a.val ≠ j - 1) :
    spliceGapStep F (corridorCfg F .adopted .drained j) a
      = corridorCfg F .adopted .drained j := by
  have hx2 := F.hx
  have haLt := a.isLt
  have hlv : (leftEndS F a).val = a.val := rfl
  have hrv : (rightEndS F a).val = a.val + 1 := rfl
  refine spliceGapStep_id F _ _ ?_
  by_cases h0 : a.val = 0
  · rw [corridorCfg_at_zero F .adopted .drained j _ (by rw [hlv]; omega),
        corridorCfg_at_cell F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact row_idleA F
  · by_cases htop : a.val + 1 = F.x
    · rw [corridorCfg_at_any F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega),
          corridorCfg_at_top F .adopted .drained j _ (by rw [hrv]; omega)]
      exact row_idleBridge F _
    · rw [corridorCfg_at_any F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega),
          corridorCfg_at_cell F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega)
            (by rw [hrv]; omega)]
      exact row_cells _

/-! ## The clean-lane configuration of each tail phase -/

/-- The literal corridor configuration of each phase of the imported tail
machine.

`convert` and `back x` receive the *same* configuration.  That identification
is forced by the row table and is the exact content of the retiming lemma
`convert_costs_one_firing` below: the physical conversion firing performs the
machine's `convert -> back x -> back (x-1)` in one step, so the phase `back x`
has no separate physical realization (`bridge_witness_stalls`). -/
def spliceConfigOf (F : SFrame) : TailPhase F.x → SpliceConfig F
  | .convert _ => corridorCfg F .adopted .bridged 0
  | .back j _ =>
      if j = F.x then corridorCfg F .adopted .bridged 0
      else corridorCfg F .adopted .drained j
  | .landed => corridorCfg F .retired .drained 0

theorem spliceConfigOf_convert (F : SFrame) (hx : 0 < F.x) :
    spliceConfigOf F (.convert hx) = corridorCfg F .adopted .bridged 0 := rfl

theorem spliceConfigOf_back_top (F : SFrame) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (h : j = F.x) :
    spliceConfigOf F (.back j hj) = corridorCfg F .adopted .bridged 0 := by
  show (if j = F.x then corridorCfg F .adopted .bridged 0
        else corridorCfg F .adopted .drained j) = _
  rw [if_pos h]

theorem spliceConfigOf_back_mid (F : SFrame) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (h : j ≠ F.x) :
    spliceConfigOf F (.back j hj) = corridorCfg F .adopted .drained j := by
  show (if j = F.x then corridorCfg F .adopted .bridged 0
        else corridorCfg F .adopted .drained j) = _
  rw [if_neg h]

theorem spliceConfigOf_landed (F : SFrame) :
    spliceConfigOf F (.landed : TailPhase F.x) = corridorCfg F .retired .drained 0 := rfl

/-! ## Retiming: the machine's `convert` step is pure accounting -/

/-- The physical retiming of the tail machine. -/
def retime (F : SFrame) : TailPhase F.x → TailPhase F.x
  | .convert hx => .back F.x ⟨hx, Nat.le_refl _⟩
  | .back j hj => .back j hj
  | .landed => .landed

theorem retime_convert (F : SFrame) (hx : 0 < F.x) :
    retime F (.convert hx) = TailPhase.advance (.convert hx) := rfl

/-- The retiming is invisible on the corridor: `convert` and `back x` are the
same physical configuration. -/
theorem spliceConfigOf_retime (F : SFrame) (p : TailPhase F.x) :
    spliceConfigOf F (retime F p) = spliceConfigOf F p := by
  cases p with
  | convert hx =>
      show spliceConfigOf F (.back F.x ⟨hx, Nat.le_refl _⟩) = corridorCfg F .adopted .bridged 0
      exact spliceConfigOf_back_top F F.x _ rfl
  | back j hj => rfl
  | landed => rfl

/-! ## Local step lemmas of the imported machine -/

private theorem advanceEdge_back {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (b : Fin x)
    (hb : b.val = j - 1) : (TailPhase.back j hj : TailPhase x).advanceEdge = some b := by
  have h1 := hj.1
  have h2 := hj.2
  have hrfl : (TailPhase.back j hj : TailPhase x).advanceEdge = some ⟨j - 1, by omega⟩ := rfl
  rw [hrfl]
  exact congrArg some (Fin.ext hb.symm)

private theorem localStep_hit {x : Nat} (s : TailPhase x) (a : Fin x)
    (hae : s.advanceEdge = some a) :
    TailPhase.localStep (fun c : Fin x => c) s a = s.advance :=
  TailPhase.localStep_advance (fun c : Fin x => c) s a hae

private theorem localStep_miss {x : Nat} (s : TailPhase x) (a b : Fin x)
    (hae : s.advanceEdge = some b) (h : b ≠ a) :
    TailPhase.localStep (fun c : Fin x => c) s a = s := by
  unfold TailPhase.localStep
  rw [hae]
  exact if_neg h

private theorem advance_back_ge {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (h2 : 2 ≤ j)
    (hj' : 1 ≤ j - 1 ∧ j - 1 ≤ x) :
    TailPhase.advance (.back j hj : TailPhase x) = .back (j - 1) hj' := by
  simp only [TailPhase.advance]
  rw [dif_pos h2]

private theorem advance_back_lt {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (h2 : ¬ 2 ≤ j) :
    TailPhase.advance (.back j hj : TailPhase x) = .landed := by
  simp only [TailPhase.advance]
  rw [dif_neg h2]

/-! ## Exact simulation of the tail machine by the literal corridor -/

/-- Exact simulation on every `back` phase and every corridor edge: the
literal pair row on the two endpoints of edge `a` performs precisely the
machine's local step. -/
theorem spliceGapStep_back (F : SFrame) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (a : Fin F.x) :
    spliceGapStep F (spliceConfigOf F (.back j hj)) a
      = spliceConfigOf F (TailPhase.localStep (fun b : Fin F.x => b) (.back j hj) a) := by
  have hx2 := F.hx
  have hj1 := hj.1
  have hj2 := hj.2
  by_cases hhit : a.val = j - 1
  · have hae : (TailPhase.back j hj : TailPhase F.x).advanceEdge = some a :=
      advanceEdge_back hj a hhit
    rw [localStep_hit _ a hae]
    by_cases h2 : 2 ≤ j
    · have hj' : 1 ≤ j - 1 ∧ j - 1 ≤ F.x := ⟨by omega, by omega⟩
      rw [advance_back_ge hj h2 hj']
      by_cases htop : j = F.x
      · rw [spliceConfigOf_back_top F j hj htop,
            spliceConfigOf_back_mid F (j - 1) hj' (by omega)]
        have hae2 : a = convEdge F := Fin.ext (by show a.val = F.x - 1; omega)
        rw [hae2, htop]
        exact step_convert F
      · rw [spliceConfigOf_back_mid F j hj htop,
            spliceConfigOf_back_mid F (j - 1) hj' (by omega)]
        exact step_carry F j h2 (by omega) a hhit
    · rw [advance_back_lt hj h2]
      have hjone : j = 1 := by omega
      subst hjone
      rw [spliceConfigOf_back_mid F 1 hj (by omega), spliceConfigOf_landed F]
      exact step_land F a (by omega)
  · have hb : (⟨j - 1, by omega⟩ : Fin F.x) ≠ a := by
      intro hz
      exact hhit (congrArg Fin.val hz).symm
    rw [localStep_miss _ a ⟨j - 1, by omega⟩ (advanceEdge_back hj _ rfl) hb]
    by_cases htop : j = F.x
    · rw [spliceConfigOf_back_top F j hj htop]
      exact step_stutter_convert F a (by omega)
    · rw [spliceConfigOf_back_mid F j hj htop]
      exact step_stutter_witness F j a hhit

/-- **Exact row/phase simulation on the corridor.**

For every undischarged phase `p` of the imported tail machine and every
corridor edge `a`, the literal splice row fired on the two endpoints of `a`
takes the clean-lane configuration of `p` to the clean-lane configuration of
the machine's own local step at the retimed phase.  The retiming is invisible
on configurations (`spliceConfigOf_retime`); it only records that the
machine's `convert` step costs no firing. -/
theorem spliceGapStep_phase (F : SFrame) (p : TailPhase F.x) (hp : 0 < p.debt)
    (a : Fin F.x) :
    spliceGapStep F (spliceConfigOf F p) a
      = spliceConfigOf F (TailPhase.localStep (fun b : Fin F.x => b) (retime F p) a) := by
  cases p with
  | convert hx =>
      have hcfg : spliceConfigOf F (.convert hx) =
          spliceConfigOf F (.back F.x ⟨hx, Nat.le_refl _⟩) :=
        (spliceConfigOf_back_top F F.x ⟨hx, Nat.le_refl _⟩ rfl).symm
      rw [hcfg]
      exact spliceGapStep_back F F.x ⟨hx, Nat.le_refl _⟩ a
  | back j hj => exact spliceGapStep_back F j hj a
  | landed => exact absurd hp (by simp [TailPhase.debt])

/-! ## The corridor inside the `n`-edge scheduler -/

/-- The corridor's own edges inside the ambient scheduler clock. -/
structure SEmbedding (F : SFrame) (n : Nat) where
  edgeAt : Fin F.x → Fin n
  inj : ∀ a b, edgeAt a = edgeAt b → a = b

theorem localStep_embed {n : Nat} (F : SFrame) (E : SEmbedding F n) (q : TailPhase F.x)
    (a : Fin F.x) :
    TailPhase.localStep E.edgeAt q (E.edgeAt a)
      = TailPhase.localStep (fun b : Fin F.x => b) q a := by
  unfold TailPhase.localStep
  cases hq : q.advanceEdge with
  | none => rfl
  | some b =>
      show (if E.edgeAt b = E.edgeAt a then q.advance else q)
          = (if b = a then q.advance else q)
      by_cases hb : b = a
      · rw [hb, if_pos rfl, if_pos rfl]
      · rw [if_neg (fun hz => hb (E.inj b a hz)), if_neg hb]

/-- Clock ticks that are not corridor edges leave the tail phase alone. -/
theorem localStep_off_corridor {n : Nat} (F : SFrame) (E : SEmbedding F n) (q : TailPhase F.x)
    (e : Fin n) (he : ∀ a : Fin F.x, E.edgeAt a ≠ e) :
    TailPhase.localStep E.edgeAt q e = q := by
  unfold TailPhase.localStep
  cases hq : q.advanceEdge with
  | none => rfl
  | some b => exact if_neg (he b)

private theorem spliceTailStep_phase {n x : Nat} (edgeAt : Fin x → Fin n) (s s' : TailState x)
    (e : Fin n) (h : spliceTailStep edgeAt s e = .active s') :
    s'.phase = TailPhase.localStep edgeAt s.phase e := by
  unfold spliceTailStep at h
  split at h
  · injection h with h1
    exact (congrArg TailState.phase h1).symm
  · cases h

private theorem spliceTailStep_success {n x : Nat} (edgeAt : Fin x → Fin n) (s : TailState x)
    (e : Fin n) (h : spliceTailStep edgeAt s e = .success) :
    TailPhase.localStep edgeAt s.phase e = .landed := by
  unfold spliceTailStep at h
  split at h
  · cases h
  · next hz => exact TailPhase.debt_eq_zero _ (by omega)

/-- The `back` phases of the imported tail machine. -/
def IsBack {x : Nat} : TailPhase x → Prop
  | .convert _ => False
  | .back _ _ => True
  | .landed => False

/-- **The corridor process is the imported tail machine.**  Every active
transition of `spliceTailStep` on a corridor edge is realized by the literal
splice row on the corridor, and the resulting machine state carries exactly
the resulting corridor configuration. -/
theorem spliceCorridor_tracks {n : Nat} (F : SFrame) (E : SEmbedding F n) (s s' : TailState F.x)
    (hs : IsBack s.phase) (a : Fin F.x)
    (hstep : spliceTailStep E.edgeAt s (E.edgeAt a) = .active s') :
    spliceGapStep F (spliceConfigOf F s.phase) a = spliceConfigOf F s'.phase := by
  have hph := spliceTailStep_phase E.edgeAt s s' (E.edgeAt a) hstep
  rw [hph, localStep_embed F E s.phase a]
  have hact := s.active
  cases hq : s.phase with
  | convert hx => rw [hq] at hs; exact hs.elim
  | back j hj => exact spliceGapStep_back F j hj a
  | landed =>
      rw [hq] at hact
      exact absurd hact (by simp [TailPhase.debt])

/-- The landing transition: the last corridor firing produces exactly the
landed configuration, in which `A` is retired. -/
theorem spliceCorridor_lands {n : Nat} (F : SFrame) (E : SEmbedding F n) (s : TailState F.x)
    (hs : IsBack s.phase) (a : Fin F.x)
    (hstep : spliceTailStep E.edgeAt s (E.edgeAt a) = .success) :
    spliceGapStep F (spliceConfigOf F s.phase) a = corridorCfg F .retired .drained 0 := by
  have hph := spliceTailStep_success E.edgeAt s (E.edgeAt a) hstep
  rw [localStep_embed F E s.phase a] at hph
  have hact := s.active
  cases hq : s.phase with
  | convert hx => rw [hq] at hs; exact hs.elim
  | back j hj =>
      rw [hq] at hph
      rw [spliceGapStep_back F j hj a, hph]
      exact spliceConfigOf_landed F
  | landed =>
      rw [hq] at hact
      exact absurd hact (by simp [TailPhase.debt])

/-! ## The transported cost of the corridor -/

/-- The corridor starts at the conversion, i.e. at the retimed phase
`back x` -- the same physical configuration as `convert`. -/
def spliceCorridorStart (F : SFrame) : TailState F.x :=
  ⟨.back F.x ⟨by have := F.hx; omega, Nat.le_refl _⟩, by
    have := F.hx
    show 0 < F.x
    omega⟩

theorem spliceCorridorStart_config (F : SFrame) :
    spliceConfigOf F (spliceCorridorStart F).phase = corridorCfg F .adopted .bridged 0 :=
  spliceConfigOf_back_top F F.x _ rfl

theorem spliceCorridorStart_isBack (F : SFrame) : IsBack (spliceCorridorStart F).phase := trivial

/-- Scale one on the physical `n`-edge scheduler for the literal corridor
process: its truncated active cost is bounded by `n^T * (n*(x+1))`, the
transported `spliceDebt` bound of the imported tail machine.  The corridor's
own start potential is `n*x`; the extra `n` is exactly the machine's
accounting-only `convert` step. -/
theorem spliceCorridor_truncatedCost_le {n : Nat} (F : SFrame) (E : SEmbedding F n) (T : Nat) :
    truncatedActiveCostNumerator (spliceTailStep E.edgeAt)
        (.active (spliceCorridorStart F)) T ≤ n ^ T * (n * (F.x + 1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (spliceTailStep E.edgeAt) 1 (spliceTailPotential n) (splice_bellman E.edgeAt)
    (.active (spliceCorridorStart F)) T
  have hstart : spliceTailPotential n (.active (spliceCorridorStart F)) = n * F.x := rfl
  rw [Nat.one_mul, hstart] at h
  have hmono : n * F.x ≤ n * (F.x + 1) := Nat.mul_le_mul_left n (by omega)
  exact Nat.le_trans h (Nat.mul_le_mul_left (n ^ T) hmono)

theorem spliceCorridor_start_potential {n : Nat} (F : SFrame) :
    spliceTailPotential n (.active (spliceCorridorStart F)) = n * F.x := rfl

theorem spliceCorridor_no_failure {n : Nat} (F : SFrame) (E : SEmbedding F n)
    (s : TailState F.x) (e : Fin n) : spliceTailStep E.edgeAt s e ≠ .failure :=
  spliceTailStep_ne_failure E.edgeAt s e

/-! ## The `(B,C)` side is framed -/

/-- The raw ring node at each corridor offset.  It does not depend on any
splice field, so it is the same in every phase of the lane. -/
def corridorRaw (F : SFrame) (k : Nat) : Node :=
  if k = 0 then aRaw F else if k = F.x then bridgeRaw F else emptyRaw

theorem corridorCfg_raw (F : SFrame) (asp bsp : SpliceCtl) (tok : Nat) (k : Fin (F.x + 1)) :
    (corridorCfg F asp bsp tok k).core.raw = corridorRaw F k.val := by
  unfold corridorCfg corridorNode corridorRaw
  by_cases h0 : k.val = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    by_cases hx : k.val = F.x
    · rw [if_pos hx, if_pos hx]
      rfl
    · rw [if_neg hx, if_neg hx]
      by_cases ht : k.val = tok
      · rw [if_pos ht]
        rfl
      · rw [if_neg ht]
        rfl

theorem spliceConfigOf_raw (F : SFrame) (q : TailPhase F.x) (k : Fin (F.x + 1)) :
    (spliceConfigOf F q k).core.raw = corridorRaw F k.val := by
  cases q with
  | convert hx => exact corridorCfg_raw F _ _ _ k
  | back j hj =>
      by_cases h : j = F.x
      · rw [spliceConfigOf_back_top F j hj h]; exact corridorCfg_raw F _ _ _ k
      · rw [spliceConfigOf_back_mid F j hj h]; exact corridorCfg_raw F _ _ _ k
  | landed => exact corridorCfg_raw F _ _ _ k

theorem spliceGapStep_frame (F : SFrame) (cfg : SpliceConfig F) (a : Fin F.x)
    (k : Fin (F.x + 1)) (h1 : k.val ≠ a.val) (h2 : k.val ≠ a.val + 1) :
    spliceGapStep F cfg a k = cfg k := by
  unfold spliceGapStep
  rw [if_neg h1, if_neg h2]

/-- **The `(B,C)` side is framed by the corridor.**

1. A corridor firing writes exactly the two offsets `a` and `a+1`, and
   `a + 1 ≤ x`: no node beyond former `B` is touched, so the whole `(B,C)`
   side is outside the corridor.
2. No corridor firing writes *any* raw ring field at all: the retirement rows
   move only the wrapper's witness and lifecycle marks.
3. In particular former `B`'s raw node -- whose clockwise port carries the
   settled old `(B,C)` verdict and whose lease is `accepted` -- is unchanged,
   and `A`'s counterclockwise port (which belongs to the *previous* gap) is
   unchanged. -/
theorem spliceCorridor_frames_BC (F : SFrame) (p : TailPhase F.x) (hp : 0 < p.debt)
    (a : Fin F.x) :
    (∀ k : Fin (F.x + 1), k.val ≠ a.val → k.val ≠ a.val + 1 →
        spliceGapStep F (spliceConfigOf F p) a k = spliceConfigOf F p k) ∧
      a.val + 1 ≤ F.x ∧
      (∀ k : Fin (F.x + 1),
        (spliceGapStep F (spliceConfigOf F p) a k).core.raw
          = (spliceConfigOf F p k).core.raw) ∧
      (spliceGapStep F (spliceConfigOf F p) a ⟨F.x, Nat.lt_succ_self _⟩).core.raw
        = bridgeRaw F ∧
      (spliceGapStep F (spliceConfigOf F p) a ⟨0, Nat.succ_pos _⟩).core.raw.ccwPort
        = some F.aCcw := by
  have hx2 := F.hx
  have hraw : ∀ k : Fin (F.x + 1),
      (spliceGapStep F (spliceConfigOf F p) a k).core.raw = corridorRaw F k.val := by
    intro k
    rw [spliceGapStep_phase F p hp a]
    exact spliceConfigOf_raw F _ k
  refine ⟨fun k h1 h2 => spliceGapStep_frame F _ a k h1 h2, a.isLt, ?_, ?_, ?_⟩
  · intro k
    rw [hraw k, spliceConfigOf_raw F p k]
  · rw [hraw ⟨F.x, Nat.lt_succ_self _⟩]
    show corridorRaw F F.x = bridgeRaw F
    unfold corridorRaw
    rw [if_neg (by omega), if_pos rfl]
  · rw [hraw ⟨0, Nat.succ_pos _⟩]
    show (corridorRaw F 0).ccwPort = some F.aCcw
    unfold corridorRaw
    rw [if_pos rfl]
    rfl

/-! ## The three mismatches, proved rather than patched

The imported machine `TailPhase x` charges `spliceDebt x = x+1` firings to the
tail.  The corridor built above executes the tail in exactly `x` firings, and
two further phases of the imported description have no literal realization at
all.  None of this is repaired by editing the machine: the mismatches are
stated and proved here, and the corrected count is `corridor_exact_firings`.
-/

/-- The bridge with an explicit witness field. -/
def bridgeW (F : SFrame) (sp : SpliceCtl) (w : RetireWitness) : SNode :=
  ⟨⟨bridgeRaw F, false, F.bCtl, .committed, .none⟩, some F.bSnap, none, sp, w, .none⟩

theorem bridgeN_eq_bridgeW (F : SFrame) (sp : SpliceCtl) : bridgeN F sp = bridgeW F sp .none := rfl

theorem spliceRule_core_of (a b : SNode)
    (h1 : ¬ FreshFlush a b) (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h9 : ¬ HandoffArm a) :
    spliceRule a b = .core (commitRule a.core b.core) := by
  have hr : srun a b =
      { rule := .core (commitRule a.core b.core)
        left := (liftPair a b (commitRow a.core b.core)).1
        right := (liftPair a b (commitRow a.core b.core)).2
        valid := .core } := by
    simp only [srun, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
      dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9]
  exact congrArg SResult.rule hr

theorem commitRule_idle_of (a b : CNode)
    (g1 : ¬ SourceAck a) (g2 : ¬ TargetCleanup a) (g3 : ¬ Legacy a b) (g4 : ¬ Launch a b)
    (g5 : ¬ Forward a b) (g6 : ¬ AtTarget a b) (g7 : ¬ Backward a b) (g8 : ¬ Deposit a b)
    (g9 : ¬ Direct a b) : commitRule a b = .idle := by
  have hr : run a b = { rule := .idle, left := a, right := b, valid := .idle } := by
    simp only [run, dif_neg g1, dif_neg g2, dif_neg g3, dif_neg g4, dif_neg g5,
      dif_neg g6, dif_neg g7, dif_neg g8, dif_neg g9]
  exact congrArg Result.rule hr

/-- **Mismatch (i).**  A retirement witness sitting *at* the bridge can never
leave it: the transport row `RetireBackward` requires an empty right endpoint,
and former `B`'s raw node is still a root.  So the phase `back x` -- "the
witness is `x` firings from `A`" -- has no literal realization, whatever the
bridge's lifecycle mark. -/
theorem row_bridgeToken (F : SFrame) (w : RetireWitness) (sp : SpliceCtl) :
    spliceRow (cellN w) (bridgeW F sp .token) = (cellN w, bridgeW F sp .token) := by
  have hcore : spliceRow (cellN w) (bridgeW F sp .token) =
      liftPair (cellN w) (bridgeW F sp .token)
        (commitRow (cellN w).core (bridgeW F sp .token).core) := by
    refine spliceRow_core_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.2.2.2.2.2
    · intro h; cases h.2.2.1.1
    · intro h; cases h.1
    · intro h; exact h.2.1 rfl
    · intro h; exact h.2.1 rfl
    · intro h; cases h.1
  have hseed : seedIn (bridgeRaw F) = .reserved := rfl
  have hidle : commitRow (cellN w).core (bridgeW F sp .token).core =
      ((cellN w).core, (bridgeW F sp .token).core) := by
    refine commitRow_idle_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1.1
    · intro h; cases h.1.1
    · intro h
      have hx : CommitIn.committed = seedIn (bridgeRaw F) := h.2.1.2
      rw [hseed] at hx
      cases hx
    · intro h; cases h.1.1
    · intro h; cases h.1.2
    · intro h; cases h.1.2
    · intro h; cases h.2.1
    · intro h; cases h.1.1
    · intro h; cases h.1.1
  exact spliceRow_stutter_of _ _ hcore hidle rfl rfl

/-- The corridor configuration in which the witness sits at the bridge. -/
def bridgeTokenCfg (F : SFrame) : SpliceConfig F :=
  fun k => if k.val = F.x then bridgeW F .drained .token
           else corridorCfg F .adopted .drained 0 k

theorem bridge_witness_stalls (F : SFrame) :
    spliceGapStep F (bridgeTokenCfg F) (convEdge F) = bridgeTokenCfg F := by
  have hx2 := F.hx
  have hlv : (leftEndS F (convEdge F)).val = F.x - 1 := rfl
  have hrv : (rightEndS F (convEdge F)).val = F.x := by
    show F.x - 1 + 1 = F.x
    omega
  have hL : bridgeTokenCfg F (leftEndS F (convEdge F)) = cellN .none := by
    unfold bridgeTokenCfg
    rw [if_neg (by rw [hlv]; omega)]
    exact corridorCfg_at_cell F _ _ _ _ (by rw [hlv]; omega) (by rw [hlv]; omega)
      (by rw [hlv]; omega)
  have hR : bridgeTokenCfg F (rightEndS F (convEdge F)) = bridgeW F .drained .token := by
    unfold bridgeTokenCfg
    rw [if_pos hrv]
  refine spliceGapStep_id F _ _ ?_
  rw [hL, hR]
  exact row_bridgeToken F .none .drained

/-- **Mismatch (ii).**  The length-one corridor stalls.  With `x = 1` there is
no capture cell between `A` and the bridge, and the single corridor edge
`(A,B)` has no enabled row at all: `RetireLaunch` demands an empty left
endpoint, `RetireDeposit` an empty right endpoint, and the table has no fused
convert-and-deposit row (the retirement analogue of `directAdopt`).  Hence
`spliceDebt 1 = 2` is not a firing count for `x = 1`; the corridor never
lands. -/
theorem corridor_length_one_stalls (cw : CwPort) (ccw : CcwPort) (inc : InControl)
    (ctl : CommitCtl) (lease : CommitIn) (hcw : cw ≠ .heldCandidate)
    (bcw : CwPort) (bout : OutControl) (bctl : CommitCtl) (snap : SnapPhase) :
    spliceRow (sRootAt cw ccw inc ctl lease .adopted .none)
        ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
          some snap, none, .bridged, .none, .none⟩
      = (sRootAt cw ccw inc ctl lease .adopted .none,
         ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
          some snap, none, .bridged, .none, .none⟩) ∧
    spliceRule (sRootAt cw ccw inc ctl lease .adopted .none)
        ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
          some snap, none, .bridged, .none, .none⟩ = .core .idle := by
  have hown : ¬ Owner (sRootAt cw ccw inc ctl lease .adopted .none).core := by
    intro h
    have hx : rawOwner (Node.root .out1 cw ccw .finalReady inc) = true := h.1
    rw [rawOwner_root_out1 cw ccw inc hcw] at hx
    cases hx
  have h1 : ¬ FreshFlush (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.1
  have h3 : ¬ FreshForward (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.1
  have h4 : ¬ RetireLaunch (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; cases h.2.1.1
  have h7 : ¬ AdoptDeposit (sRootAt cw ccw inc ctl lease .adopted .none)
      ⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ := by intro h; exact h.2.1 rfl
  have h8 : ¬ DirectAdopt (sRootAt cw ccw inc ctl lease .adopted .none) := by
    intro h; exact h.2.1 rfl
  have h9 : ¬ HandoffArm (sRootAt cw ccw inc ctl lease .adopted .none) := by
    intro h; cases h.1
  have hseed : seedIn (Node.root .in0 bcw .heldCandidate bout .accepted) = .reserved := rfl
  have g1 : ¬ SourceAck (sRootAt cw ccw inc ctl lease .adopted .none).core :=
    fun h => hown h.1
  have g2 : ¬ TargetCleanup (sRootAt cw ccw inc ctl lease .adopted .none).core := by
    intro h; cases h.1.1
  have g3 : ¬ Legacy (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := by
    intro h
    have hx : CommitIn.committed = seedIn (Node.root .in0 bcw .heldCandidate bout .accepted) :=
      h.2.1.2
    rw [hseed] at hx
    cases hx
  have g4 : ¬ Launch (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := fun h => hown h.1
  have g5 : ¬ Forward (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := by
    intro h; cases h.1.1
  have g6 : ¬ AtTarget (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := by
    intro h; cases h.1.1
  have g7 : ¬ Backward (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := by
    intro h; cases h.1.1
  have g8 : ¬ Deposit (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := fun h => hown h.1
  have g9 : ¬ Direct (sRootAt cw ccw inc ctl lease .adopted .none).core
      (⟨⟨.root .in0 bcw .heldCandidate bout .accepted, false, bctl, .committed, .none⟩,
        some snap, none, .bridged, .none, .none⟩ : SNode).core := fun h => hown h.1
  have hidle := commitRow_idle_of _ _ g1 g2 g3 g4 g5 g6 g7 g8 g9
  refine ⟨spliceRow_stutter_of _ _ (spliceRow_core_of _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9) hidle rfl rfl,
    ?_⟩
  rw [spliceRule_core_of _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9,
    commitRule_idle_of _ _ g1 g2 g3 g4 g5 g6 g7 g8 g9]

/-- **Mismatch (iii): the conversion firing performs two machine steps.**

One firing of the bridge edge takes the `convert` configuration to the
configuration of `back (x-1)`, i.e. it executes `convert -> back x ->
back (x-1)`: the conversion row `retireLaunch` both spends the bridge and
hands the witness to the last capture cell.  So the machine's `convert` step
is charged but never executed, and after the *first* corridor firing the
machine still claims `x-1+1` remaining firings while `x-1` remain. -/
theorem convert_costs_one_firing (F : SFrame) (hx : 0 < F.x)
    (hj : 1 ≤ F.x - 1 ∧ F.x - 1 ≤ F.x) :
    spliceGapStep F (spliceConfigOf F (.convert hx)) (convEdge F)
        = spliceConfigOf F (.back (F.x - 1) hj) ∧
      TailPhase.advance (TailPhase.advance (.convert hx))
        = (.back (F.x - 1) hj : TailPhase F.x) ∧
      TailPhase.advance (.convert hx) ≠ (.back (F.x - 1) hj : TailPhase F.x) ∧
      (TailPhase.convert hx).debt = spliceDebt F.x ∧
      (TailPhase.back (F.x - 1) hj : TailPhase F.x).debt + 2 = spliceDebt F.x := by
  have hx2 := F.hx
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · rw [spliceConfigOf_convert F hx, spliceConfigOf_back_mid F (F.x - 1) hj (by omega)]
    exact step_convert F
  · show TailPhase.advance (TailPhase.back F.x ⟨hx, Nat.le_refl _⟩) = _
    exact advance_back_ge ⟨hx, Nat.le_refl _⟩ (by omega) hj
  · intro hbad
    have hz : (TailPhase.back F.x ⟨hx, Nat.le_refl _⟩ : TailPhase F.x)
        = (.back (F.x - 1) hj : TailPhase F.x) := hbad
    injection hz with h1
    omega
  · show F.x - 1 + 2 = F.x + 1
    omega

/-- **The corrected count.**  From the conversion the corridor lands in
exactly `x` firings -- one conversion and `x-1` witness transfers, the last of
which is the deposit at `A` -- while the imported machine charges
`spliceDebt x = x+1`.  The surplus is exactly the accounting-only `convert`
step; the charge is therefore conservative, never optimistic. -/
theorem corridor_exact_firings (F : SFrame) :
    (spliceCorridorStart F).phase.debt = F.x ∧
      TailPhase.iter F.x (spliceCorridorStart F).phase = .landed ∧
      (∀ k, k < F.x → TailPhase.iter k (spliceCorridorStart F).phase ≠ .landed) ∧
      spliceDebt F.x = F.x + 1 ∧
      (spliceCorridorStart F).phase.debt + 1 = spliceDebt F.x := by
  have hx2 := F.hx
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · apply TailPhase.debt_eq_zero
    rw [TailPhase.debt_iter]
    show F.x - F.x = 0
    omega
  · intro k hk hbad
    have hd : (TailPhase.iter k (spliceCorridorStart F).phase).debt
        = (spliceCorridorStart F).phase.debt - k := TailPhase.debt_iter k _
    rw [hbad] at hd
    have hzero : (TailPhase.landed : TailPhase F.x).debt = 0 := rfl
    have hstart : (spliceCorridorStart F).phase.debt = F.x := rfl
    omega

/-- **Mismatch (iv): `landed` is not a physical fixed point.**  The machine's
terminal phase stutters, but the corridor keeps firing: at the landed
configuration the edge `(A, cell 1)` fires `handoffArm`, which rearms `A` for
the fresh episode (`A.cw := toSend`, declaration marked unflushed).  That
firing belongs to the next episode, not to the splice tail, which is why the
tail process stops at the landing (`spliceCorridor_lands`). -/
theorem landed_continues_with_handoff (F : SFrame) (a : Fin F.x) (ha : a.val = 0) :
    spliceGapStep F (spliceConfigOf F .landed) a (leftEndS F a)
        = sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed ∧
      spliceGapStep F (spliceConfigOf F (.landed : TailPhase F.x)) a
        ≠ spliceConfigOf F (.landed : TailPhase F.x) := by
  have hx2 := F.hx
  have hlv : (leftEndS F a).val = 0 := ha
  have hrv : (rightEndS F a).val = 1 := by
    show a.val + 1 = 1
    omega
  have hL : spliceConfigOf F (.landed : TailPhase F.x) (leftEndS F a) = aNode F .retired := by
    rw [spliceConfigOf_landed F]
    exact corridorCfg_at_zero F _ _ _ _ hlv
  have hR : spliceConfigOf F (.landed : TailPhase F.x) (rightEndS F a) = cellN .none := by
    rw [spliceConfigOf_landed F]
    exact corridorCfg_at_cell F _ _ _ _ (by rw [hrv]; omega) (by rw [hrv]; omega)
      (by rw [hrv]; omega)
  have hrow : spliceRow (spliceConfigOf F (.landed : TailPhase F.x) (leftEndS F a))
      (spliceConfigOf F (.landed : TailPhase F.x) (rightEndS F a))
      = (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed, cellN .none) := by
    rw [hL, hR]
    exact splice_handoff_arm F.aCw F.aCcw F.aInc F.aCtl F.aLease
  have hfirst : spliceGapStep F (spliceConfigOf F (.landed : TailPhase F.x)) a (leftEndS F a)
      = sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed := by
    unfold spliceGapStep
    rw [if_pos (show (leftEndS F a).val = a.val from rfl), hrow]
  refine ⟨hfirst, ?_⟩
  intro hbad
  have hz : (spliceGapStep F (spliceConfigOf F (.landed : TailPhase F.x)) a (leftEndS F a)).splice
      = (spliceConfigOf F (.landed : TailPhase F.x) (leftEndS F a)).splice :=
    congrArg (fun c : SpliceConfig F => (c (leftEndS F a)).splice) hbad
  rw [hfirst, hL] at hz
  cases hz

/-! ## The corridor row encodes the tail machine in the ambient clock -/

/-- **The literal corridor row is the tail machine's local step**, read
through the corridor's embedding into the `n`-edge scheduler clock. -/
theorem spliceGapStep_encodes {n : Nat} (F : SFrame) (E : SEmbedding F n) (p : TailPhase F.x)
    (hp : 0 < p.debt) (a : Fin F.x) :
    spliceGapStep F (spliceConfigOf F p) a
      = spliceConfigOf F (TailPhase.localStep E.edgeAt (retime F p) (E.edgeAt a)) := by
  rw [localStep_embed F E (retime F p) a]
  exact spliceGapStep_phase F p hp a

/-- A clock tick that is not a corridor edge changes no corridor
configuration: the tail is framed by the rest of the ring. -/
theorem splice_offCorridor_frames {n : Nat} (F : SFrame) (E : SEmbedding F n)
    (p : TailPhase F.x) (e : Fin n) (he : ∀ a : Fin F.x, E.edgeAt a ≠ e) :
    spliceConfigOf F (TailPhase.localStep E.edgeAt (retime F p) e) = spliceConfigOf F p := by
  rw [localStep_off_corridor F E (retime F p) e he]
  exact spliceConfigOf_retime F p

/-! ## A literal corridor, to witness that none of this is vacuous -/

/-- A concrete corridor of length two: `A`, one former capture cell, the
bridge.  `aCw = waiting` is the value the adopt row writes for an outstanding
old `(B,C)` episode. -/
def demoFrame : SFrame where
  x := 2
  hx := by omega
  aCw := .waiting
  haCw := by intro h; cases h
  aCcw := .free
  aInc := .open
  aCtl := .committedReceived
  aLease := .committed
  bCw := .heldDenial
  hbCw := Or.inl rfl
  bOut := .home
  bCtl := .clean
  bSnap := ⟨.toSend, .home⟩

/-- Two literal firings run the whole tail of a length-two corridor: the
bridge edge converts and transports, the `A` edge deposits and retires. -/
theorem demo_run :
    spliceGapStep demoFrame
        (spliceGapStep demoFrame (corridorCfg demoFrame .adopted .bridged 0)
          (convEdge demoFrame)) ⟨0, Nat.succ_pos 1⟩
      = corridorCfg demoFrame .retired .drained 0 := by
  rw [step_convert demoFrame]
  exact step_land demoFrame ⟨0, Nat.succ_pos 1⟩ rfl

/-- The same two firings, as the imported machine sees them. -/
theorem demo_debt :
    (spliceCorridorStart demoFrame).phase.debt = 2 ∧ spliceDebt demoFrame.x = 3 :=
  ⟨rfl, rfl⟩

/-! ## Axiom audit -/

#print axioms spliceGapStep_phase
#print axioms spliceGapStep_back
#print axioms spliceGapStep_encodes
#print axioms splice_offCorridor_frames
#print axioms spliceCorridor_tracks
#print axioms spliceCorridor_lands
#print axioms spliceCorridor_truncatedCost_le
#print axioms spliceCorridor_frames_BC
#print axioms row_convert
#print axioms row_land
#print axioms row_carry
#print axioms step_convert
#print axioms convert_costs_one_firing
#print axioms corridor_exact_firings
#print axioms bridge_witness_stalls
#print axioms corridor_length_one_stalls
#print axioms landed_continues_with_handoff
#print axioms demo_run

end ShortGapSpliceCorridor
