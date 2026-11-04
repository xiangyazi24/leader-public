import Leader.L3.Target

/-!
Partial kernel-port of the start-clock table.

The definitions below are total and reproduce the eight-shape
piecewise potential. The local source-row lemmas are stated
against the literal SerResult. No general row-congruence theorem,
one-edge drift theorem, or stochastic bound is asserted here.
-/

namespace L3

set_option autoImplicit false

/-- C/NONE, C/PENDING, C/INTERNAL_OK, C/LEAF_OK,
    B/NEW, B/WAIT, B/DONE, F, respectively. -/
def serShape (s : Ser) : Fin 8 :=
  match s.phase with
  | .C =>
    match s.probe with
    | .NONE => 0
    | .PENDING => 1
    | .INTERNAL_OK => 2
    | .LEAF_OK => 3
  | .B =>
    match s.out with
    | .NEW => 4
    | .WAIT => 5
    | .DONE => 6
  | .F => 7

/-- The eight-shape quotient ignores cert, wphase, C's out,
    B's probe, and all of F's out/probe. -/
theorem serShape_field_congr (a b : Ser)
    (hp : a.phase = b.phase)
    (ho : a.out = b.out)
    (hq : a.probe = b.probe) :
    serShape a = serShape b := by
  cases a with
  | mk pa oa qa ca wa =>
    cases b with
    | mk pb ob qb cb wb =>
      cases hp
      cases ho
      cases hq
      rfl

theorem serShape_canonical (s : Ser) :
    serShape (serCanonicalC s) = (0 : Fin 8) := rfl

theorem serShape_enter_broadcast (s : Ser) (p : SerWPhase) :
    serShape (serEnterB s p) = (4 : Fin 8) := rfl

theorem serShape_enter_return (s : Ser) :
    serShape (serEnterF s) = (7 : Fin 8) := rfl

theorem serShape_challenge_right (x y : Ser) :
    serShape (serChallengeWrite x y).2 = (1 : Fin 8) := rfl

theorem serShape_challenge_left (x y : Ser)
    (hx : x.phase = .B) :
    serShape (serChallengeWrite x y).1 = (5 : Fin 8) := by
  simp [serShape, serChallengeWrite, hx]

/-- Read offsets 0,...,n-1. The recursion consumes one unit of
    fuel before inspecting the next offset; it returns n if
    the whole length-n word consists of shape B/DONE. -/
def firstNonDone (w : Nat → Fin 8) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
    if (w k).val = 6 then
      firstNonDone w fuel (k + 1)
    else k

theorem firstNonDone_zero (w : Nat → Fin 8) (k : Nat) :
    firstNonDone w 0 k = k := rfl

/-- The earlier explicit total piecewise start-clock potential.
    Subtraction is Nat subtraction; the intended bound is for n>=4.
    The final x=6 branch is unreachable when k<n and all
    preceding shapes were tested by firstNonDone. -/
def startPsiWord (n : Nat) (cert : SerCert)
    (w : Nat → Fin 8) : Nat :=
  if cert = .REQUESTED then 1
  else if cert = .IDLE then 2
  else if ((w 0).val ≤ 3 ∨ (w 0).val = 7) then 3
  else
    let k := firstNonDone w n 0
    let x := (w k).val
    let remainder : Nat :=
      if k = n then n + 3
      else if x = 7 then k
      else if x ≤ 3 then
        if k + 1 = n then n + 2 else 5 * n - 2 - 4 * k
      else if x = 4 then
        if k + 1 = n then n + 3 else 5 * n - 6 - 4 * k
      else if x = 5 then
        if k + 1 = n then n + 3
        else
          let y := (w (k + 1)).val
          if y = 1 then
            if k + 2 = n then n + 1
            else
              5 * n - 11 - 4 * k +
                (if 4 ≤ (w (k + 2)).val then 4 else 3)
          else if y = 2 then
            if k + 2 = n then n + 4
            else 5 * n - 9 - 4 * k
          else if y = 3 then k + 2
          else
            if k + 2 = n then n + 2
            else 5 * n - 6 - 4 * k
      else 0
    remainder + 2

/-- The actual word is read clockwise from the supplied physical
    root, not from the numerical site index zero. -/
def startPsi {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) : Nat :=
  startPsiWord n (s root).ser.cert
    (fun k => serShape (s (PPL.shiftRight ring root k)).ser)

theorem startPsiWord_requested (n : Nat) (w : Nat → Fin 8) :
    startPsiWord n .REQUESTED w = 1 := rfl

theorem startPsiWord_idle (n : Nat) (w : Nat → Fin 8) :
    startPsiWord n .IDLE w = 2 := rfl

theorem startPsi_requested {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hc : (s root).ser.cert = .REQUESTED) :
    startPsi ring root s = 1 := by
  simp [startPsi, startPsiWord, hc]

theorem startPsi_idle {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hc : (s root).ser.cert = .IDLE) :
    startPsi ring root s = 2 := by
  simp [startPsi, startPsiWord, hc]

/-- These two field projections are definitional consequences of
    Target.pairW. They do not yet invoke native geometry. -/
theorem pairW_ser_left {c : Compiled} (x y : ProjW c) :
    (pairW x y).1.ser = (serW x y).x := rfl

theorem pairW_ser_right {c : Compiled} (x y : ProjW c) :
    (pairW x y).2.ser = (serW x y).y := rfl

/-- Selected source coordinates use the real pairW. -/
theorem phiW_ser_source {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) :
    ((phiW ring s e) e).ser =
      (serW (s e) (s (ring.rightNeighbor e))).x := by
  simp [phiW, projectedEdge, pairW]

/-- Selected responder coordinates use the same real pairW.
    The endpoint distinctness premise is explicit. -/
theorem phiW_ser_target {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) (hneq : ring.rightNeighbor e ≠ e) :
    ((phiW ring s e) (ring.rightNeighbor e)).ser =
      (serW (s e) (s (ring.rightNeighbor e))).y := by
  simp [phiW, projectedEdge, pairW, hneq]

/-! Literal serializer cases with explicit POST-E endpoint bits.
    These are not yet the all-Cartesian eight-shape transition table. -/

/-- FULL S0, ROOT_IN, old root cert IDLE. -/
theorem serRootIncomingIdle {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hc : y.ser.cert = .IDLE) :
    (serW x y).row = "S0" ∧
    (serW x y).y.cert = .REQUESTED := by
  simp [serW, serializerStep, ProjW.lift, hx, hy, hc]

/-- FULL S5, ROOT_IN, old root cert not IDLE. -/
theorem serRootIncomingNonidle {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hc : y.ser.cert ≠ .IDLE) :
    (serW x y).row = "S5" ∧
    (serW x y).y.cert = y.ser.cert := by
  simp [serW, serializerStep, ProjW.lift, hx, hy, hc]

/-- FULL S1, ROOT_OUT. Serializer S1 is independent of SI lease;
    the lease only chooses the fresh wphase. -/
theorem serRootOutgoingStart {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED) :
    (serW x y).row = "S1" ∧
    (serW x y).x.cert = .RUNNING ∧
    serShape ((serW x y).x) = (5 : Fin 8) ∧
    serShape ((serW x y).y) = (1 : Fin 8) := by
  simp [serW, serializerStep, ProjW.lift,
    serTbStar, serShape, hx, hy, hc]

/-- FULL SR for the two cert and two C/F phase choices. -/
theorem serRootOutgoingRecovery {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .IDLE ∨ x.ser.cert = .RUNNING)
    (hp : x.ser.phase = .C ∨ x.ser.phase = .F) :
    (serW x y).row = "SR" ∧
    (serW x y).x.cert = .IDLE ∧
    serShape ((serW x y).x) = (5 : Fin 8) ∧
    serShape ((serW x y).y) = (1 : Fin 8) := by
  rcases hc with hc | hc <;>
    rcases hp with hp | hp <;>
    simp [serW, serializerStep, ProjW.lift,
      serTbStar, serShape, hx, hy, hc, hp]

/-- FULL S6, root B/DONE sees F and was not REQUESTED. -/
theorem serRootOutgoingDone {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert ≠ .REQUESTED)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hf : y.ser.phase = .F) :
    (serW x y).row = "S6" ∧
    (serW x y).x.cert = .IDLE ∧
    (serW x y).x.phase = .C := by
  simp [serW, serializerStep, ProjW.lift,
    serShape, hx, hy, hc, hp, ho, hf]

/-- One nontrivial S2N subrow: B/NEW challenges any right phase. -/
theorem serInternalNewChallenge {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .NEW) :
    (serW x y).row = "S2N" ∧
    serShape ((serW x y).x) = (5 : Fin 8) ∧
    serShape ((serW x y).y) = (1 : Fin 8) := by
  cases hphase : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift,
      serChallengeWrite, serShape, hx, hy, hp, ho, hphase]

/-- The corresponding S2R B/NEW subrow, excluding the higher
    priority S1. -/
theorem serRootOutgoingNewChallenge {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert ≠ .REQUESTED)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .NEW) :
    (serW x y).row = "S2R" ∧
    serShape ((serW x y).x) = (5 : Fin 8) ∧
    serShape ((serW x y).y) = (1 : Fin 8) := by
  cases hphase : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift,
      serChallengeWrite, serShape, hx, hy, hc, hp, ho, hphase]

/-- FULL S3 observation: a C/PENDING source sees a C responder. -/
theorem serInternalObservation {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hp : x.ser.phase = .C)
    (hq : x.ser.probe = .PENDING)
    (hr : y.ser.phase = .C) :
    (serW x y).row = "S3" ∧
    serShape ((serW x y).x) = (2 : Fin 8) ∧
    serShape ((serW x y).y) = serShape y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    serShape, hx, hy, hp, hq, hr]

/-- FULL S4 deletion: a returning F source sees a B responder. -/
theorem serInternalReturnErase {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hp : x.ser.phase = .F)
    (hr : y.ser.phase = .B) :
    (serW x y).row = "S4" ∧
    serShape ((serW x y).x) = (7 : Fin 8) ∧
    serShape ((serW x y).y) = (0 : Fin 8) := by
  simp [serW, serializerStep, ProjW.lift,
    serCanonicalC, serShape, hx, hy, hp, hr]

end L3

namespace L3

set_option autoImplicit false

/-!
The root serializer is coarser than serShape: S6 keeps the OLD
probe even when it changes the phase to C (CertRows.lean:280).
The root's C/F probe never participates in serializer control.
All three transition functions below are total on their finite types.
-/

inductive RootStage
  | freshB
  | waitingB
  | completedB
  | nonB
  deriving DecidableEq, Repr

structure RootClass where
  cert : SerCert
  stage : RootStage
  deriving DecidableEq, Repr

def rootStage (s : Ser) : RootStage :=
  match s.phase with
  | .C => .nonB
  | .F => .nonB
  | .B =>
    match s.out with
    | .NEW => .freshB
    | .WAIT => .waitingB
    | .DONE => .completedB

def rootClass (s : Ser) : RootClass :=
  { cert := s.cert, stage := rootStage s }

/-- INTERNAL: FULL:353-376; codes are the original serShape values.
    The B/DONE+F case returns F,F only for an internal edge. -/
def followerPair (x y : Fin 8) : Fin 8 × Fin 8 :=
  if x.val = 4 then (5, 1)
  else if x.val = 5 then
    if y.val = 1 then (5, 1)
    else if y.val = 2 then (6, 4)
    else if y.val = 3 then (6, 7)
    else (5, 1)
  else if x.val = 6 then
    if y.val = 7 then (7, 7)
    else if 4 ≤ y.val then (x, y)
    else (5, 1)
  else if x.val = 1 then
    if y.val ≤ 3 then (2, y) else (x, 0)
  else if x.val ≤ 3 then
    if 4 ≤ y.val then (x, 0) else (x, y)
  else if x.val = 7 then
    if 4 ≤ y.val then (x, 0) else (x, y)
  else (x, y)

/-- ROOT_OUT: FULL:336-352.
    none denotes the actual S1 serializer row (either lease kind).
    A returned root class discards the root C/F probe, not the
    follower's source probe. -/
def rootOut (r : RootClass) (y : Fin 8) :
    Option (RootClass × Fin 8) :=
  if r.cert = .REQUESTED then none
  else
    match r.stage with
    | .nonB =>
      some ({ cert := .IDLE, stage := .waitingB }, 1)
    | .freshB =>
      some ({ cert := r.cert, stage := .waitingB }, 1)
    | .waitingB =>
      if y.val = 1 then some (r, y)
      else if y.val = 2 then
        some ({ cert := r.cert, stage := .completedB }, 4)
      else if y.val = 3 then
        some ({ cert := r.cert, stage := .completedB }, 7)
      else some ({ cert := r.cert, stage := .waitingB }, 1)
    | .completedB =>
      if y.val = 7 then
        some ({ cert := .IDLE, stage := .nonB }, y)
      else if 4 ≤ y.val then some (r, y)
      else some ({ cert := r.cert, stage := .waitingB }, 1)

/-- ROOT_IN: FULL:328-335.
    S0 frames the incoming follower and requests the idle root.
    S5 changes C/PENDING to C/LEAF_OK, or B to C/NONE,
    without changing the nonidle root class. -/
def rootIn (x : Fin 8) (r : RootClass) :
    Fin 8 × RootClass :=
  if r.cert = .IDLE then
    (x, { cert := .REQUESTED, stage := r.stage })
  else if x.val = 1 then (3, r)
  else if 4 ≤ x.val ∧ x.val ≤ 6 then (0, r)
  else (x, r)

/-- The exact root-out terminal discriminator on the table. -/
theorem rootOut_none_of_requested (r : RootClass) (y : Fin 8)
    (h : r.cert = .REQUESTED) :
    rootOut r y = none := by
  simp [rootOut, h]

/-- The original S6 theorem only proved the new phase is C.
    That suffices for the coarse root stage even with OLD probe. -/
theorem rootStage_c (s : Ser)
    (h : s.phase = .C) :
    rootStage s = .nonB := by
  simp [rootStage, h]

/-- S1 + coarse root: a requested root selects none. -/
theorem rootOut_literal_start {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED) :
    (serW x y).row = "S1" ∧
      rootOut (rootClass x.ser) (serShape y.ser) = none := by
  have hs := serRootOutgoingStart x y hx hy hc
  constructor
  · exact hs.1
  · exact rootOut_none_of_requested _ _ hc

/-- S6 + coarse root, preserving rather than resetting probe. -/
theorem rootClass_literal_six {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert ≠ .REQUESTED)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hf : y.ser.phase = .F) :
    rootClass ((serW x y).x) =
      { cert := .IDLE, stage := .nonB } := by
  have hs := serRootOutgoingDone x y hx hy hc hp ho hf
  simp [rootClass, rootStage, hs.2.1, hs.2.2]

/-!
Three exhaustive bridges on the literal serW, not a
restatement of the table. Their case proofs split only finite
serializer fields; all ignored SI, lease, wphase, cert fields remain
arbitrary.
-/

/-- Every INTERNAL row, including S2N, S3, S4 and frames. -/
theorem followerPair_literal {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false) :
    (serShape ((serW x y).x), serShape ((serW x y).y)) =
      followerPair (serShape x.ser) (serShape y.ser) := by
  -- Split the phases first and simplify: the row and its branch are then fixed. A cell in phase C
  -- is read only through its probe, in phase B only through its out, in phase F not at all
  -- (`serShape` and the INTERNAL guards), so only that field is split next.
  cases hpx : x.ser.phase <;>
    cases hpy : y.ser.phase <;>
    (try simp [serW, serializerStep, ProjW.lift,
      serShape, followerPair, serChallengeWrite, serEnterB, serEnterF, serCanonicalC, hx, hy, hpx, hpy]) <;>
    (first
      | (have _ : x.ser.phase = .C := hpx; cases hqx : x.ser.probe)
      | (have _ : x.ser.phase = .B := hpx; cases hox : x.ser.out)
      | skip) <;>
    (first
      | (have _ : y.ser.phase = .C := hpy; cases hqy : y.ser.probe)
      | (have _ : y.ser.phase = .B := hpy; cases hoy : y.ser.out)
      | skip) <;>
    (try simp [serW, serializerStep, ProjW.lift,
      serShape, followerPair, serChallengeWrite, serEnterB, serEnterF, serCanonicalC, hx, hy, *]) <;>
    decide

/-- Every ROOT_IN row, including S0/S5 and their first-match choice. -/
theorem rootIn_literal {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true) :
    (serShape ((serW x y).x), rootClass ((serW x y).y)) =
      rootIn (serShape x.ser) (rootClass y.ser) := by
  -- Split the phases (and the root's cert) first and simplify: the row and its branch are then
  -- fixed and the remaining splits work on the small residual term.
  cases hpx : x.ser.phase <;>
    cases hpy : y.ser.phase <;>
    cases hcy : y.ser.cert <;>
    (try simp [serW, serializerStep, ProjW.lift,
      serShape, rootClass, rootStage, rootIn, serCanonicalC, hx, hy, hpx, hpy, hcy]) <;>
    cases hoy : y.ser.out <;>
    cases hox : x.ser.out <;>
    cases hqx : x.ser.probe <;>
    (try simp [serW, serializerStep, ProjW.lift,
      serShape, rootClass, rootStage, rootIn, serCanonicalC, hx, hy, hpx, hpy, hcy, hoy, hox, hqx]) <;>
    decide

/-- Every ROOT_OUT row. Only the S1 row is represented by none.
    In particular S6 is projected to (IDLE, nonB) even when the
    root's OLD C-probe is not NONE. -/
theorem rootOut_literal {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false) :
    (if (serW x y).row = "S1" then none
     else some (rootClass ((serW x y).x),
                serShape ((serW x y).y))) =
      rootOut (rootClass x.ser) (serShape y.ser) := by
  -- Split the phases (and the root's cert) first and simplify: the row and its branch are then
  -- fixed and the remaining splits work on the small residual term.
  cases hpx : x.ser.phase <;>
    cases hpy : y.ser.phase <;>
    cases hcx : x.ser.cert <;>
    (try simp [serW, serializerStep, ProjW.lift,
      rootClass, rootStage, rootOut, serShape, serTbStar, serChallengeWrite, serEnterB, serEnterF,
      serCanonicalC, hx, hy, hpx, hpy, hcx]) <;>
    cases hox : x.ser.out <;>
    cases hoy : y.ser.out <;>
    cases hqy : y.ser.probe <;>
    (try simp [serW, serializerStep, ProjW.lift,
      rootClass, rootStage, rootOut, serShape, serTbStar, serChallengeWrite, serEnterB, serEnterF,
      serCanonicalC, hx, hy, hpx, hpy, hcx, hox, hoy, hqy]) <;>
    decide

/-- Shape-and-cert framing at a nonselected site is independent
    of the native fixed-root proof still required in item (3). -/
theorem phiW_ser_remote {c : Compiled} {n : Nat}
    (ring : DirectedRing n)
    (s : Fin n → ProjW c) (e i : Fin n)
    (hi : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    ((phiW ring s e) i).ser = (s i).ser := by
  simp [phiW, projectedEdge, hi, hj]

end L3


namespace L3

set_option autoImplicit false

/-!
The post-E native leader is exactly the selected pairW native
coordinate. The fixed root is required on the phiW successor, as
in WOriginHistory.next (Target.lean:796-800).
-/

/-- A directed edge has distinct endpoints when n >= 2. -/
theorem clockNeighborDifferent {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- Actual POST-E source bit equals the source native bit in phiW. -/
theorem clockPostSourceNative {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l =
      ((phiW ring s e) e).native.l := by
  calc
    (postW (s e) (s (ring.rightNeighbor e))).eX.l =
        (pairW (s e) (s (ring.rightNeighbor e))).1.native.l := rfl
    _ = ((phiW ring s e) e).native.l := by
      simp only [phiW, projectedEdge, if_pos rfl]

/-- Actual POST-E responder bit equals the responder native bit in phiW. -/
theorem clockPostTargetNative {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
      ((phiW ring s e) (ring.rightNeighbor e)).native.l := by
  calc
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
        (pairW (s e) (s (ring.rightNeighbor e))).2.native.l := rfl
    _ = ((phiW ring s e) (ring.rightNeighbor e)).native.l := by
      simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]

/-- The POST-E source bit is true precisely at the fixed root. -/
theorem clockPostSourceIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring s e)) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l = true ↔
      e = root := by
  constructor
  · intro h
    apply hfixed.2.1 e
    calc
      ((phiW ring s e) e).native.l =
          (postW (s e) (s (ring.rightNeighbor e))).eX.l :=
        (clockPostSourceNative ring s e).symm
      _ = true := h
  · intro he
    subst e
    calc
      (postW (s root) (s (ring.rightNeighbor root))).eX.l =
          ((phiW ring s root) root).native.l :=
        clockPostSourceNative ring s root
      _ = true := hfixed.1

/-- The POST-E responder bit is true precisely at the fixed root. -/
theorem clockPostTargetIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e)) :
    (postW (s e) (s (ring.rightNeighbor e))).eY.l = true ↔
      ring.rightNeighbor e = root := by
  have hne := clockNeighborDifferent ring hn e
  constructor
  · intro h
    apply hfixed.2.1 (ring.rightNeighbor e)
    calc
      ((phiW ring s e) (ring.rightNeighbor e)).native.l =
          (postW (s e) (s (ring.rightNeighbor e))).eY.l :=
        (clockPostTargetNative ring s e hne).symm
      _ = true := h
  · intro hj
    calc
      (postW (s e) (s (ring.rightNeighbor e))).eY.l =
          ((phiW ring s e) (ring.rightNeighbor e)).native.l :=
        clockPostTargetNative ring s e hne
      _ = true := by simpa only [hj] using hfixed.1

private theorem clockBoolFalse (b : Bool)
    (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

/-- ROOT_OUT: the POST-E flags are (true, false). -/
theorem clockPostOutgoing {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e = root) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l = true ∧
    (postW (s e) (s (ring.rightNeighbor e))).eY.l = false := by
  have hx := (clockPostSourceIff ring root s e hfixed).2 he
  have hj : ring.rightNeighbor e ≠ root := by
    intro hj
    apply clockNeighborDifferent ring hn e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := he.symm
  refine ⟨hx, clockBoolFalse _ ?_⟩
  intro h
  exact hj ((clockPostTargetIff ring root s e hn hfixed).1 h)

/-- ROOT_IN: the POST-E flags are (false, true). -/
theorem clockPostIncoming {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hj : ring.rightNeighbor e = root) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l = false ∧
    (postW (s e) (s (ring.rightNeighbor e))).eY.l = true := by
  have he : e ≠ root := by
    intro he
    apply clockNeighborDifferent ring hn e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := he.symm
  have hy := (clockPostTargetIff ring root s e hn hfixed).2 hj
  refine ⟨clockBoolFalse _ ?_, hy⟩
  intro h
  exact he ((clockPostSourceIff ring root s e hfixed).1 h)

/-- INTERNAL: the POST-E flags are (false, false). -/
theorem clockPostInternal {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l = false ∧
    (postW (s e) (s (ring.rightNeighbor e))).eY.l = false := by
  constructor
  · apply clockBoolFalse
    intro h
    exact he ((clockPostSourceIff ring root s e hfixed).1 h)
  · apply clockBoolFalse
    intro h
    exact hj ((clockPostTargetIff ring root s e hn hfixed).1 h)

/-- Exhaustive edge-kind trichotomy from the native post-step premise. -/
theorem clockPostTrichotomy {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e)) :
    (e = root ∧
      (postW (s e) (s (ring.rightNeighbor e))).eX.l = true ∧
      (postW (s e) (s (ring.rightNeighbor e))).eY.l = false) ∨
    (ring.rightNeighbor e = root ∧
      (postW (s e) (s (ring.rightNeighbor e))).eX.l = false ∧
      (postW (s e) (s (ring.rightNeighbor e))).eY.l = true) ∨
    (e ≠ root ∧ ring.rightNeighbor e ≠ root ∧
      (postW (s e) (s (ring.rightNeighbor e))).eX.l = false ∧
      (postW (s e) (s (ring.rightNeighbor e))).eY.l = false) := by
  by_cases he : e = root
  · exact Or.inl ⟨he, clockPostOutgoing ring root s e hn hfixed he⟩
  · by_cases hj : ring.rightNeighbor e = root
    · exact Or.inr (Or.inl
        ⟨hj, clockPostIncoming ring root s e hn hfixed hj⟩)
    · exact Or.inr (Or.inr
        ⟨he, hj, clockPostInternal ring root s e hn hfixed he hj⟩)

/-! Clockwise coordinates, copied locally from the proved NativeSector
geometry (without importing EWord). -/

def clockSite {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (k : Nat) : Fin n :=
  PPL.shiftRight ring root k

def clockPosition {n : Nat}
    (ring : DirectedRing n) (root i : Fin n) : Fin n :=
  ⟨PPL.cyclicOffset ring root i, Nat.mod_lt _ ring.hn⟩

theorem clockSiteZero {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    clockSite ring root 0 = root := by
  apply Fin.ext
  simp [clockSite, PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

theorem clockPositionSite {n : Nat}
    (ring : DirectedRing n) (root k : Fin n) :
    clockPosition ring root (clockSite ring root k.val) = k := by
  apply Fin.ext
  change (((root.val + k.val) % n + n - root.val) % n) = k.val
  by_cases hs : root.val + k.val < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : root.val + k.val + n - root.val = n + k.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt k.isLt]
  · have hge : n ≤ root.val + k.val := by omega
    have hlt : root.val + k.val - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : root.val + k.val - n + n - root.val = k.val := by omega
    rw [he, Nat.mod_eq_of_lt k.isLt]

theorem clockSitePosition {n : Nat}
    (ring : DirectedRing n) (root i : Fin n) :
    clockSite ring root (clockPosition ring root i).val = i := by
  apply Fin.ext
  change (root.val + ((i.val + n - root.val) % n)) % n = i.val
  by_cases hri : root.val ≤ i.val
  · have he : i.val + n - root.val = n + (i.val - root.val) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : i.val - root.val < n)]
    have hh : root.val + (i.val - root.val) = i.val := by omega
    rw [hh, Nat.mod_eq_of_lt i.isLt]
  · have hlt : i.val + n - root.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hh : root.val + (i.val + n - root.val) = i.val + n := by omega
    rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem clockSiteInjective {n : Nat}
    (ring : DirectedRing n) (root a b : Fin n)
    (h : clockSite ring root a.val = clockSite ring root b.val) :
    a = b := by
  have hp := congrArg (clockPosition ring root) h
  rw [clockPositionSite, clockPositionSite] at hp
  exact hp

theorem clockSiteNext {n : Nat}
    (ring : DirectedRing n) (root k : Fin n) :
    clockSite ring root (ring.rightNeighbor k).val =
      ring.rightNeighbor (clockSite ring root k.val) := by
  apply Fin.ext
  change (root.val + (k.val + 1) % n) % n =
    ((root.val + k.val) % n + 1) % n
  calc
    (root.val + (k.val + 1) % n) % n =
        ((k.val + 1) % n + root.val) % n := by rw [Nat.add_comm]
    _ = (k.val + 1 + root.val) % n := Nat.mod_add_mod _ _ _
    _ = (root.val + k.val + 1) % n := by congr 1; omega
    _ = ((root.val + k.val) % n + 1) % n :=
      (Nat.mod_add_mod _ _ _).symm

theorem clockPositionNext {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    clockPosition ring root (ring.rightNeighbor e) =
      ring.rightNeighbor (clockPosition ring root e) := by
  have h := clockSiteNext ring root (clockPosition ring root e)
  rw [clockSitePosition] at h
  have hp := congrArg (clockPosition ring root) h
  rw [clockPositionSite] at hp
  exact hp.symm

/-- A physical edge is consecutive in root-relative offsets. -/
theorem clockEdgeOffsets {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    e = clockSite ring root (clockPosition ring root e).val ∧
    ring.rightNeighbor e =
      clockSite ring root
        (ring.rightNeighbor (clockPosition ring root e)).val := by
  constructor
  · exact (clockSitePosition ring root e).symm
  · simpa only [clockSitePosition] using
      (clockSiteNext ring root (clockPosition ring root e)).symm

def clockShapeAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (k : Fin n) : Fin 8 :=
  serShape (s (clockSite ring root k.val)).ser

/-- INTERNAL table lifted to the real pairW on the physical edge. -/
theorem clockPhiInternalTable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root) :
    (serShape ((phiW ring s e) e).ser,
     serShape ((phiW ring s e) (ring.rightNeighbor e)).ser) =
    followerPair (serShape (s e).ser)
      (serShape (s (ring.rightNeighbor e)).ser) := by
  have hf := clockPostInternal ring root s e hn hfixed he hj
  rw [phiW_ser_source ring s e,
    phiW_ser_target ring s e (clockNeighborDifferent ring hn e)]
  exact followerPair_literal (s e) (s (ring.rightNeighbor e))
    hf.1 hf.2

/-- ROOT_IN source and coarse-root responder lifted to the real pairW. -/
theorem clockPhiIncomingTable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hj : ring.rightNeighbor e = root) :
    (serShape ((phiW ring s e) e).ser,
     rootClass ((phiW ring s e) (ring.rightNeighbor e)).ser) =
    rootIn (serShape (s e).ser)
      (rootClass (s (ring.rightNeighbor e)).ser) := by
  have hf := clockPostIncoming ring root s e hn hfixed hj
  rw [phiW_ser_source ring s e,
    phiW_ser_target ring s e (clockNeighborDifferent ring hn e)]
  exact rootIn_literal (s e) (s (ring.rightNeighbor e))
    hf.1 hf.2

/-- ROOT_OUT table: none iff the actual serializer row is S1. -/
theorem clockPhiOutgoingTable {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e = root) :
    (if (serW (s e) (s (ring.rightNeighbor e))).row = "S1" then none
     else some (rootClass ((phiW ring s e) e).ser,
       serShape ((phiW ring s e) (ring.rightNeighbor e)).ser)) =
    rootOut (rootClass (s e).ser)
      (serShape (s (ring.rightNeighbor e)).ser) := by
  have hf := clockPostOutgoing ring root s e hn hfixed he
  rw [phiW_ser_source ring s e,
    phiW_ser_target ring s e (clockNeighborDifferent ring hn e)]
  exact rootOut_literal (s e) (s (ring.rightNeighbor e))
    hf.1 hf.2

/-- INTERNAL table at any root-relative offset p. -/
theorem clockPhiInternalOffset {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root p : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p.val)))
    (he : clockSite ring root p.val ≠ root)
    (hj : ring.rightNeighbor (clockSite ring root p.val) ≠ root) :
    (clockShapeAt ring root
      (phiW ring s (clockSite ring root p.val)) p,
     clockShapeAt ring root
       (phiW ring s (clockSite ring root p.val))
       (ring.rightNeighbor p)) =
    followerPair (clockShapeAt ring root s p)
      (clockShapeAt ring root s (ring.rightNeighbor p)) := by
  simpa only [clockShapeAt, clockSiteNext] using
    (clockPhiInternalTable ring root s
      (clockSite ring root p.val) hn hfixed he hj)

/-- ROOT_IN table at an offset whose successor is the root. -/
theorem clockPhiIncomingOffset {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root p : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p.val)))
    (hj : ring.rightNeighbor (clockSite ring root p.val) = root) :
    (clockShapeAt ring root
      (phiW ring s (clockSite ring root p.val)) p,
     rootClass
       ((phiW ring s (clockSite ring root p.val)) root).ser) =
    rootIn (clockShapeAt ring root s p) (rootClass (s root).ser) := by
  have htab := clockPhiIncomingTable ring root s
    (clockSite ring root p.val) hn hfixed hj
  simpa only [clockShapeAt, hj] using htab

/-- ROOT_OUT table at the root-relative offset zero. -/
theorem clockPhiOutgoingOffset {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root p : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p.val)))
    (he : clockSite ring root p.val = root) :
    (if (serW (s (clockSite ring root p.val))
          (s (ring.rightNeighbor (clockSite ring root p.val)))).row =
          "S1" then none
     else some (rootClass
       ((phiW ring s (clockSite ring root p.val)) root).ser,
       clockShapeAt ring root
         (phiW ring s (clockSite ring root p.val))
         (ring.rightNeighbor p))) =
    rootOut (rootClass (s root).ser)
      (clockShapeAt ring root s (ring.rightNeighbor p)) := by
  have htab := clockPhiOutgoingTable ring root s
    (clockSite ring root p.val) hn hfixed he
  simpa only [clockShapeAt, clockSiteNext, he] using htab

/-- Every other offset retains its exact old serializer shape. -/
theorem clockPhiRemoteOffset {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e k : Fin n)
    (hk : k ≠ clockPosition ring root e)
    (hj : k ≠ ring.rightNeighbor (clockPosition ring root e)) :
    clockShapeAt ring root (phiW ring s e) k =
      clockShapeAt ring root s k := by
  have hsource : clockSite ring root k.val ≠ e := by
    intro he
    have hp := congrArg (clockPosition ring root) he
    rw [clockPositionSite] at hp
    exact hk hp
  have htarget :
      clockSite ring root k.val ≠ ring.rightNeighbor e := by
    intro he
    have hp := congrArg (clockPosition ring root) he
    rw [clockPositionSite, clockPositionNext] at hp
    exact hj hp
  simpa only [clockShapeAt] using
    congrArg serShape
      (phiW_ser_remote ring s e
        (clockSite ring root k.val) hsource htarget)

end L3


namespace L3

set_option autoImplicit false

/-!
Only structural firstNonDone lemmas, two exact frame cases, and
the IDLE ROOT_IN cert case are asserted. In particular no general
frontier monotonicity or strict nominated-edge lemma is asserted.
-/

/-- The first unfinished position lies in the scanned interval,
including its right endpoint when the entire interval is done. -/
theorem clockFirstNonDoneRange (w : Nat → Fin 8) :
    ∀ fuel k, k ≤ firstNonDone w fuel k ∧
      firstNonDone w fuel k ≤ k + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    exact ⟨Nat.le_refl k, Nat.le_refl k⟩
  | succ fuel ih =>
    intro k
    by_cases h : (w k).val = 6
    · obtain ⟨hl, hu⟩ := ih (k + 1)
      simp only [firstNonDone, if_pos h]
      constructor <;> omega
    · simp [firstNonDone, h]

/-- All earlier scanned positions are shape B/DONE. -/
theorem clockFirstNonDonePrefixDone (w : Nat → Fin 8) :
    ∀ fuel start i, start ≤ i →
      i < firstNonDone w fuel start → (w i).val = 6 := by
  intro fuel
  induction fuel with
  | zero =>
    intro start i hlo hhi
    change i < start at hhi
    omega
  | succ fuel ih =>
    intro start i hlo hhi
    by_cases hs : (w start).val = 6
    · simp only [firstNonDone, if_pos hs] at hhi
      by_cases he : i = start
      · subst i
        exact hs
      · have hlo' : start + 1 ≤ i := by omega
        exact ih (start + 1) i hlo' hhi
    · simp only [firstNonDone, if_neg hs] at hhi
      omega

/-- Unless the search exhausted its fuel, the returned shape is not B/DONE. -/
theorem clockFirstNonDoneFrontNotDone (w : Nat → Fin 8) :
    ∀ fuel start,
      firstNonDone w fuel start < start + fuel →
      (w (firstNonDone w fuel start)).val ≠ 6 := by
  intro fuel
  induction fuel with
  | zero =>
    intro start h
    change start < start at h
    omega
  | succ fuel ih =>
    intro start h
    by_cases hs : (w start).val = 6
    · have hn :
          firstNonDone w fuel (start + 1) <
            start + Nat.succ fuel := by
        change (if (w start).val = 6 then
          firstNonDone w fuel (start + 1) else start) <
          start + Nat.succ fuel at h
        simpa only [if_pos hs] using h
      have ht :
          firstNonDone w fuel (start + 1) <
            (start + 1) + fuel := by omega
      have hh := ih (start + 1) ht
      simpa only [firstNonDone, if_pos hs] using hh
    · simp only [firstNonDone, if_neg hs]
      exact hs

/-- A prefix of B/DONE followed by a non-B/DONE site locates the
    first unfinished position for every fuel that reaches that site. -/
theorem clockFirstNonDoneAt (w : Nat → Fin 8) :
    ∀ fuel start stop, stop < fuel →
      (∀ i, i < stop → (w (start + i)).val = 6) →
      (w (start + stop)).val ≠ 6 →
      firstNonDone w fuel start = start + stop := by
  intro fuel
  induction fuel with
  | zero =>
    intro start stop hstop _ _
    omega
  | succ fuel ih =>
    intro start stop hstop hprefix hfront
    cases stop with
    | zero =>
      have hn : (w start).val ≠ 6 := by
        simpa only [Nat.add_zero] using hfront
      simp only [firstNonDone, if_neg hn, Nat.add_zero]
    | succ stop =>
      have hd : (w start).val = 6 := by
        have hh := hprefix 0 (by omega)
        simpa only [Nat.add_zero] using hh
      have hp :
          ∀ i, i < stop → (w (start + 1 + i)).val = 6 := by
        intro i hi
        have hh := hprefix (i + 1) (by omega)
        have heq : start + 1 + i = start + (i + 1) := by omega
        rw [heq]
        exact hh
      have hf : (w (start + 1 + stop)).val ≠ 6 := by
        have heq :
            start + 1 + stop = start + Nat.succ stop := by omega
        rw [heq]
        exact hfront
      have htail : stop < fuel := by omega
      have hres := ih (start + 1) stop htail hp hf
      calc
        firstNonDone w (Nat.succ fuel) start =
            firstNonDone w fuel (start + 1) := by
          simp only [firstNonDone, if_pos hd]
        _ = start + 1 + stop := hres
        _ = start + Nat.succ stop := by omega

/-- Agreeing through the old frontier preserves the firstNonDone index.
    No agreement anywhere after that frontier is required. -/
theorem clockFirstNonDoneStablePrefix
    (w v : Nat → Fin 8) (n k : Nat)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hag : ∀ i, i ≤ k → w i = v i) :
    firstNonDone v n 0 = k := by
  have hpre : ∀ i, i < k → (w i).val = 6 := by
    intro i hi
    have hh : i < firstNonDone w n 0 := by
      simpa only [hfirst] using hi
    exact clockFirstNonDonePrefixDone w n 0 i (by omega) hh
  have hbound : firstNonDone w n 0 < 0 + n := by
    simpa only [hfirst, Nat.zero_add] using hk
  have hfront : (w k).val ≠ 6 := by
    have hh := clockFirstNonDoneFrontNotDone w n 0 hbound
    simpa only [hfirst] using hh
  have hpreV : ∀ i, i < k → (v i).val = 6 := by
    intro i hi
    calc
      (v i).val = (w i).val :=
        congrArg Fin.val (hag i (by omega)).symm
      _ = 6 := hpre i hi
  have hfrontV : (v k).val ≠ 6 := by
    intro hdone
    apply hfront
    calc
      (w k).val = (v k).val :=
        congrArg Fin.val (hag k (by omega))
      _ = 6 := hdone
  have hh := clockFirstNonDoneAt v n 0 k hk
    (by
      intro i hi
      simpa only [Nat.zero_add] using hpreV i hi)
    (by simpa only [Nat.zero_add] using hfrontV)
  simpa only [Nat.zero_add] using hh

/-- For k < n, the start potential reads only the prefix through k+2.
    Positions strictly beyond k+2 cannot affect either the frontier or
    the two lookahead tests. -/
theorem clockPsiWordLocality
    (n : Nat) (cert : SerCert) (w v : Nat → Fin 8)
    (k : Nat)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hag : ∀ i, i ≤ k + 2 → w i = v i) :
    startPsiWord n cert w = startPsiWord n cert v := by
  have hnew : firstNonDone v n 0 = k :=
    clockFirstNonDoneStablePrefix w v n k hk hfirst
      (by
        intro i hi
        exact hag i (by omega))
  have hzero : w 0 = v 0 := hag 0 (by omega)
  have hx : w k = v k := hag k (by omega)
  have hy : w (k + 1) = v (k + 1) := hag (k + 1) (by omega)
  have hz : w (k + 2) = v (k + 2) := hag (k + 2) (by omega)
  simp only [startPsiWord, hzero, hfirst, hnew, hx, hy, hz]

/-- Functional write at one follower position. The root is not stored
    in this word; it is carried separately in RootClass. -/
def clockWrite (w : Nat → Fin 8) (p : Nat) (x : Fin 8) :
    Nat → Fin 8 :=
  fun i => if i = p then x else w i

theorem clockWriteSelf (w : Nat → Fin 8) (p : Nat) :
    clockWrite w p (w p) = w := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [clockWrite]
  · simp [clockWrite, hi]

/-- Two arbitrary writes strictly beyond k+2 frame the start
    potential. This is the complete remote-pair locality case. -/
theorem clockPsiRemotePair
    (n : Nat) (cert : SerCert) (w : Nat → Fin 8)
    (k p : Nat) (x y : Fin 8)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hp : k + 2 < p) :
    startPsiWord n cert
      (clockWrite (clockWrite w p x) (p + 1) y) =
      startPsiWord n cert w := by
  have hlocal : startPsiWord n cert w =
      startPsiWord n cert
        (clockWrite (clockWrite w p x) (p + 1) y) := by
    apply clockPsiWordLocality n cert w
      (clockWrite (clockWrite w p x) (p + 1) y)
      k hk hfirst
    intro i hi
    have hne : i ≠ p := by omega
    have hne' : i ≠ p + 1 := by omega
    simp [clockWrite, hne, hne']
  exact hlocal.symm

/-- A pair strictly inside the B/DONE prefix is B/DONE,B/DONE. -/
theorem clockFirstNonDoneTwoDone
    (w : Nat → Fin 8) (n p : Nat)
    (hp : p + 1 < firstNonDone w n 0) :
    w p = (6 : Fin 8) ∧ w (p + 1) = (6 : Fin 8) := by
  constructor
  · apply Fin.ext
    change (w p).val = 6
    exact clockFirstNonDonePrefixDone w n 0 p (by omega) (by omega)
  · apply Fin.ext
    change (w (p + 1)).val = 6
    exact clockFirstNonDonePrefixDone w n 0 (p + 1)
      (by omega) (by omega)

/-- INTERNAL's B/DONE,B/DONE pair is an exact frame. -/
theorem clockFollowerDonePair
    (w : Nat → Fin 8) (n p : Nat)
    (hp : p + 1 < firstNonDone w n 0) :
    followerPair (w p) (w (p + 1)) =
      (w p, w (p + 1)) := by
  obtain ⟨hx, hy⟩ := clockFirstNonDoneTwoDone w n p hp
  have hframe : followerPair (6 : Fin 8) (6 : Fin 8) =
      ((6 : Fin 8), (6 : Fin 8)) := by decide
  simpa only [hx, hy] using hframe

/-- INTERNAL update strictly inside the B/DONE prefix leaves
    the entire abstract word, hence its potential, unchanged. -/
theorem clockPsiInternalInsidePrefix
    (n : Nat) (cert : SerCert) (w : Nat → Fin 8)
    (p : Nat)
    (hp : p + 1 < firstNonDone w n 0) :
    startPsiWord n cert
      (clockWrite
        (clockWrite w p (followerPair (w p) (w (p + 1))).1)
        (p + 1) (followerPair (w p) (w (p + 1))).2) =
      startPsiWord n cert w := by
  have hframe := clockFollowerDonePair w n p hp
  have hx := congrArg Prod.fst hframe
  have hy := congrArg Prod.snd hframe
  simp only [hx, hy, clockWriteSelf]

/-- INTERNAL update strictly beyond k+2 leaves Psi unchanged.
    The two rewritten cells need no further table case analysis. -/
theorem clockPsiInternalRemote
    (n : Nat) (cert : SerCert) (w : Nat → Fin 8)
    (k p : Nat)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hp : k + 2 < p) :
    startPsiWord n cert
      (clockWrite
        (clockWrite w p (followerPair (w p) (w (p + 1))).1)
        (p + 1) (followerPair (w p) (w (p + 1))).2) =
      startPsiWord n cert w := by
  exact clockPsiRemotePair n cert w k p
    (followerPair (w p) (w (p + 1))).1
    (followerPair (w p) (w (p + 1))).2
    hk hfirst hp

/-- Canonical root shape for the abstract table. Any C or F shape
    represents nonB because startPsiWord ignores its exact probe. -/
def clockRootShape (r : RootClass) : Fin 8 :=
  match r.stage with
  | .nonB => 0
  | .freshB => 4
  | .waitingB => 5
  | .completedB => 6

def clockAbstractWord (r : RootClass) (w : Nat → Fin 8) :
    Nat → Fin 8 :=
  fun i => if i = 0 then clockRootShape r else w i

def clockAbstractPsi (n : Nat) (r : RootClass)
    (w : Nat → Fin 8) : Nat :=
  startPsiWord n r.cert (clockAbstractWord r w)

/-- ROOT_IN's S0 case: an idle root becomes REQUESTED. The
    potential goes from 2 to 1 independently of the follower word. -/
theorem clockIncomingIdleDecrease
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (h : r.cert = .IDLE) :
    clockAbstractPsi n (rootIn (w (n - 1)) r).2
      (clockWrite w (n - 1) (rootIn (w (n - 1)) r).1) ≤
    clockAbstractPsi n r w := by
  have hc : (rootIn (w (n - 1)) r).2.cert = .REQUESTED := by
    simp [rootIn, h]
  unfold clockAbstractPsi
  simp [startPsiWord, hc, h]

end L3


namespace L3

set_option autoImplicit false

/-!
A finite-window affine decomposition of the potential and the
first genuinely frontier-facing INTERNAL strict row. This
does not assert general edgewise monotonicity or drift.
-/

/-- The affine piece selected by the first non-B/DONE offset.
Its only variable forms are n+c, k+c, 5*n-c-4*k, and zero. -/
def clockWindowLinear (n k : Nat) (x y : Fin 8) : Nat :=
  if k = n then n + 3
  else if x.val = 7 then k
  else if x.val ≤ 3 then
    if k + 1 = n then n + 2 else 5 * n - 2 - 4 * k
  else if x.val = 4 then
    if k + 1 = n then n + 3 else 5 * n - 6 - 4 * k
  else if x.val = 5 then
    if k + 1 = n then n + 3
    else if y.val = 1 then
      if k + 2 = n then n + 1 else 5 * n - 11 - 4 * k
    else if y.val = 2 then
      if k + 2 = n then n + 4 else 5 * n - 9 - 4 * k
    else if y.val = 3 then k + 2
    else if k + 2 = n then n + 2
    else 5 * n - 6 - 4 * k
  else 0

/-- The bounded finite-window correction: normally two tickets;
in the single B/WAIT, PENDING, bulk row it is five or six tickets. -/
def clockWindowTip (n k : Nat) (x y z : Fin 8) : Nat :=
  if k = n then 2
  else if x.val = 7 then 2
  else if x.val ≤ 3 then 2
  else if x.val = 4 then 2
  else if x.val = 5 then
    if k + 1 = n then 2
    else if y.val = 1 then
      if k + 2 = n then 2
      else (if 4 ≤ z.val then 4 else 3) + 2
    else 2
  else 2

/-- Numeral values of the shape alphabet, for simp on window tables. -/
@[simp] private theorem clockFinValOne : ((1 : Fin 8) : Nat) = 1 := rfl
@[simp] private theorem clockFinValTwo : ((2 : Fin 8) : Nat) = 2 := rfl
@[simp] private theorem clockFinValThree : ((3 : Fin 8) : Nat) = 3 := rfl
@[simp] private theorem clockFinValFour : ((4 : Fin 8) : Nat) = 4 := rfl
@[simp] private theorem clockFinValFive : ((5 : Fin 8) : Nat) = 5 := rfl
@[simp] private theorem clockFinValSix : ((6 : Fin 8) : Nat) = 6 := rfl
@[simp] private theorem clockFinValSeven : ((7 : Fin 8) : Nat) = 7 := rfl

/-- The original unsimplified thirteen-row window table. In
particular, n is tested before reading x, and the lookahead
coordinates are never used outside B/WAIT. -/
def clockWindowRemainder
    (n k : Nat) (x y z : Fin 8) : Nat :=
  (if k = n then n + 3
   else if x.val = 7 then k
   else if x.val ≤ 3 then
     if k + 1 = n then n + 2 else 5 * n - 2 - 4 * k
   else if x.val = 4 then
     if k + 1 = n then n + 3 else 5 * n - 6 - 4 * k
   else if x.val = 5 then
     if k + 1 = n then n + 3
     else if y.val = 1 then
       if k + 2 = n then n + 1
       else 5 * n - 11 - 4 * k +
         (if 4 ≤ z.val then 4 else 3)
     else if y.val = 2 then
       if k + 2 = n then n + 4 else 5 * n - 9 - 4 * k
     else if y.val = 3 then k + 2
     else if k + 2 = n then n + 2
     else 5 * n - 6 - 4 * k
   else 0) + 2

/-- One complete affine decomposition, including all terminal cases.
No assumptions on n or k are needed for this syntactic identity. -/
theorem clockWindowAffine
    (n k : Nat) (x y z : Fin 8) :
    clockWindowRemainder n k x y z =
      clockWindowLinear n k x y +
        clockWindowTip n k x y z := by
  by_cases hn : k = n
  · simp [clockWindowRemainder, clockWindowLinear, clockWindowTip, hn]
  · by_cases hf : x.val = 7
    · simp [clockWindowRemainder, clockWindowLinear, clockWindowTip, hn, hf]
    · by_cases hc : x.val ≤ 3
      · simp [clockWindowRemainder, clockWindowLinear, clockWindowTip,
          hn, hf, hc]
      · by_cases hb : x.val = 4
        · simp [clockWindowRemainder, clockWindowLinear, clockWindowTip,
            hn, hf, hc, hb]
        · by_cases hw : x.val = 5
          · by_cases hl : k + 1 = n
            · simp [clockWindowRemainder, clockWindowLinear, clockWindowTip,
                hn, hf, hc, hb, hw, hl]
            · by_cases hp : y.val = 1
              · by_cases hpen : k + 2 = n
                · simp [clockWindowRemainder, clockWindowLinear,
                    clockWindowTip, hn, hf, hc, hb, hw, hl, hp, hpen]
                · simp [clockWindowRemainder, clockWindowLinear,
                    clockWindowTip, hn, hf, hc, hb, hw, hl, hp, hpen,
                    Nat.add_assoc]
              · by_cases hi : y.val = 2
                · simp [clockWindowRemainder, clockWindowLinear,
                    clockWindowTip, hn, hf, hc, hb, hw, hl, hp, hi]
                · by_cases hd : y.val = 3
                  · simp [clockWindowRemainder, clockWindowLinear,
                      clockWindowTip, hn, hf, hc, hb, hw, hl, hp, hi, hd]
                  · simp [clockWindowRemainder, clockWindowLinear,
                      clockWindowTip, hn, hf, hc, hb, hw, hl, hp, hi, hd]
          · simp [clockWindowRemainder, clockWindowLinear,
              clockWindowTip, hn, hf, hc, hb, hw]

/-- Complete window reduction for a RUNNING root in B phase:
no data to the right of k+2 is read. -/
theorem clockPsiRunningWindow
    (n k : Nat) (w : Nat → Fin 8)
    (hroot : ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7))
    (hfirst : firstNonDone w n 0 = k) :
    startPsiWord n .RUNNING w =
      clockWindowRemainder n k (w k) (w (k + 1)) (w (k + 2)) := by
  simp [startPsiWord, hroot, hfirst, clockWindowRemainder]

/-- The entire start clock, exactly one finite-window
correction plus its selected affine term. This is valid for every
natural n, including n=0 and full B/DONE words. -/
theorem clockPsiRunningAffine
    (n k : Nat) (w : Nat → Fin 8)
    (hroot : ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7))
    (hfirst : firstNonDone w n 0 = k) :
    startPsiWord n .RUNNING w =
      clockWindowLinear n k (w k) (w (k + 1)) +
        clockWindowTip n k (w k) (w (k + 1)) (w (k + 2)) := by
  rw [clockPsiRunningWindow n k w hroot hfirst]
  exact clockWindowAffine n k (w k) (w (k + 1)) (w (k + 2))

/-- A RUNNING nonB root has constant potential three. -/
theorem clockPsiRunningNonB
    (n : Nat) (w : Nat → Fin 8)
    (hroot : (w 0).val ≤ 3 ∨ (w 0).val = 7) :
    startPsiWord n .RUNNING w = 3 := by
  simp [startPsiWord, hroot]

/-- Abstract root-stage version of the affine decomposition. -/
theorem clockAbstractWindowAffine
    (n k : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hc : r.cert = .RUNNING)
    (hs : r.stage ≠ .nonB)
    (hfirst : firstNonDone (clockAbstractWord r w) n 0 = k) :
    clockAbstractPsi n r w =
      clockWindowLinear n k
        (clockAbstractWord r w k)
        (clockAbstractWord r w (k + 1)) +
      clockWindowTip n k
        (clockAbstractWord r w k)
        (clockAbstractWord r w (k + 1))
        (clockAbstractWord r w (k + 2)) := by
  have hroot :
      ¬ (((clockAbstractWord r w) 0).val ≤ 3 ∨
         ((clockAbstractWord r w) 0).val = 7) := by
    cases hstage : r.stage <;>
      simp [clockAbstractWord, clockRootShape, hstage] at *
  unfold clockAbstractPsi
  rw [hc]
  exact clockPsiRunningAffine n k (clockAbstractWord r w)
    hroot hfirst

/-! Strict local finite-window inequalities. Their proofs use only
the two end tests k+1=n, k+2=n, and linear Nat arithmetic. -/

/-- B/NEW at k: the challenger (B/WAIT,PENDING) has at least one
fewer ticket, for any two lookahead shapes. -/
theorem clockWindowFreshStrict
    (n k : Nat) (y z : Fin 8)
    (hn : 4 ≤ n) (hb : k + 1 < n) :
    clockWindowRemainder n k 5 1 z + 1 ≤
      clockWindowRemainder n k 4 y z := by
  have hk : k ≠ n := by omega
  have hl : k + 1 ≠ n := by omega
  by_cases hp : k + 2 = n
  · simp [clockWindowRemainder, hk, hl, hp] <;> omega
  · have hbulk : k + 2 < n := by omega
    by_cases hz : 4 ≤ z.val
    · simp [clockWindowRemainder, hk, hl, hp, hz] <;> omega
    · simp [clockWindowRemainder, hk, hl, hp, hz] <;> omega

/-- B/WAIT observing INTERNAL_OK: (B/DONE,B/NEW), so the
frontier moves from k to k+1 and loses exactly one ticket. -/
theorem clockWindowWaitInternalStrict
    (n k : Nat) (y z : Fin 8)
    (hn : 4 ≤ n) (hb : k + 1 < n) :
    clockWindowRemainder n (k + 1) 4 y z + 1 ≤
      clockWindowRemainder n k 5 2 z := by
  have hk : k ≠ n := by omega
  have hl : k + 1 ≠ n := by omega
  by_cases hp : k + 2 = n
  · simp [clockWindowRemainder, hk, hl, hp, Nat.add_assoc] <;> omega
  · have hbulk : k + 2 < n := by omega
    simp [clockWindowRemainder, hk, hl, hp, Nat.add_assoc] <;> omega

/-- B/WAIT observing LEAF_OK: (B/DONE,F), so the frontier
moves from k to k+1 and loses exactly one ticket. -/
theorem clockWindowWaitLeafStrict
    (n k : Nat) (y z : Fin 8)
    (hn : 4 ≤ n) (hb : k + 1 < n) :
    clockWindowRemainder n (k + 1) 7 y z + 1 ≤
      clockWindowRemainder n k 5 3 z := by
  have hk : k ≠ n := by omega
  have hl : k + 1 ≠ n := by omega
  simp [clockWindowRemainder, hk, hl, Nat.add_assoc] <;> omega

/-- In all other non-PENDING responder shapes, B/WAIT issues a
new challenge, and the PENDING window is strictly cheaper. -/
theorem clockWindowWaitOtherStrict
    (n k : Nat) (y z : Fin 8)
    (hn : 4 ≤ n) (hb : k + 1 < n)
    (hyP : y.val ≠ 1)
    (hyI : y.val ≠ 2)
    (hyL : y.val ≠ 3) :
    clockWindowRemainder n k 5 1 z + 1 ≤
      clockWindowRemainder n k 5 y z := by
  have hk : k ≠ n := by omega
  have hl : k + 1 ≠ n := by omega
  by_cases hp : k + 2 = n
  · simp [clockWindowRemainder, hk, hl, hp, hyP, hyI, hyL] <;> omega
  · have hbulk : k + 2 < n := by omega
    by_cases hz : 4 ≤ z.val
    · simp [clockWindowRemainder, hk, hl, hp, hz,
        hyP, hyI, hyL] <;> omega
    · simp [clockWindowRemainder, hk, hl, hp, hz,
        hyP, hyI, hyL] <;> omega

/-- Actual abstract INTERNAL update of two adjacent followers. -/
def clockInternalWord (w : Nat → Fin 8) (p : Nat) :
    Nat → Fin 8 :=
  clockWrite
    (clockWrite w p (followerPair (w p) (w (p + 1))).1)
    (p + 1) (followerPair (w p) (w (p + 1))).2

theorem clockInternalWordSource (w : Nat → Fin 8) (p : Nat) :
    clockInternalWord w p p =
      (followerPair (w p) (w (p + 1))).1 := by
  have h : p ≠ p + 1 := by omega
  simp [clockInternalWord, clockWrite, h]

theorem clockInternalWordTarget (w : Nat → Fin 8) (p : Nat) :
    clockInternalWord w p (p + 1) =
      (followerPair (w p) (w (p + 1))).2 := by
  simp [clockInternalWord, clockWrite]

theorem clockInternalWordRemote (w : Nat → Fin 8) (p i : Nat)
    (hi : i ≠ p) (hj : i ≠ p + 1) :
    clockInternalWord w p i = w i := by
  simp [clockInternalWord, clockWrite, hi, hj]

/-- Updating the first unfinished follower without completing it
does not move the frontier. This uses the old prefix theorem, not
a guessed local-search equation. -/
theorem clockInternalFrontierStable
    (n k : Nat) (w : Nat → Fin 8)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hnotdone : (clockInternalWord w k k).val ≠ 6) :
    firstNonDone (clockInternalWord w k) n 0 = k := by
  have hpre : ∀ i, i < k →
      (clockInternalWord w k i).val = 6 := by
    intro i hi
    have hsrc : (w i).val = 6 :=
      clockFirstNonDonePrefixDone w n 0 i (by omega)
        (by omega)
    have hremote : clockInternalWord w k i = w i :=
      clockInternalWordRemote w k i (by omega) (by omega)
    rw [hremote]
    exact hsrc
  have hnew := clockFirstNonDoneAt
    (clockInternalWord w k) n 0 k hk
    (by
      intro i hi
      simpa only [Nat.zero_add] using hpre i hi)
    (by simpa only [Nat.zero_add] using hnotdone)
  simpa only [Nat.zero_add] using hnew

/-- First genuine internal frontier row:
a B/NEW frontier served by its outgoing edge loses at least one
Psi ticket. No assumption on the arbitrary suffix is required. -/
theorem clockInternalFrontierFreshStrict
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n)
    (hpositive : 0 < k)
    (hnext : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hx : w k = (4 : Fin 8)) :
    startPsiWord n .RUNNING (clockInternalWord w k) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockInternalWord w k
  have hpair : followerPair (w k) (w (k + 1)) =
      ((5 : Fin 8), (1 : Fin 8)) := by
    rw [hx]
    rfl
  have hsource : v k = (5 : Fin 8) := by
    dsimp [v]
    rw [clockInternalWordSource, hpair]
  have htarget : v (k + 1) = (1 : Fin 8) := by
    dsimp [v]
    rw [clockInternalWordTarget, hpair]
  have hthird : v (k + 2) = w (k + 2) :=
    clockInternalWordRemote w k (k + 2)
      (by omega) (by omega)
  have hk : k < n := by omega
  have hnotdone : (v k).val ≠ 6 := by
    rw [hsource]
    decide
  have hfrontV : firstNonDone v n 0 = k :=
    clockInternalFrontierStable n k w hk hfirst hnotdone
  have hb : (w 0).val = 6 := by
    exact clockFirstNonDonePrefixDone w n 0 0 (by omega)
      (by omega)
  have hbV : (v 0).val = 6 := by
    have hremote : v 0 = w 0 :=
      clockInternalWordRemote w k 0
        (by omega) (by omega)
    rw [hremote]
    exact hb
  have hr : ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by
    omega
  have hrV : ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
    omega
  have hold := clockPsiRunningWindow n k w hr hfirst
  have hnew := clockPsiRunningWindow n k v hrV hfrontV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hnew, hold, hsource, htarget, hthird, hx]
  exact clockWindowFreshStrict n k (w (k + 1)) (w (k + 2))
    hn hnext

end L3


namespace L3

set_option autoImplicit false

/-!
We first prove exact word framing, then certify two finite 8x8
window mirrors, and then lift the B/WAIT, INTERNAL_OK and LEAF_OK
rows to genuine all-n word-frontier advances.

IMPORTANT correction to the proposed frontier trichotomy:
a B/DONE source followed by F at the old frontier changes to F,F,
so the first unfinished index can move LEFT by one. The certified
closed n=4 witness below shows k=2 -> k'=1. This is a strict
decrease of Psi, not a counterexample to the proposed trichotomy.
-/

/-- An exact identity row of the two-cell transition produces the
    identical infinite word; there is no need to bound the suffix. -/
theorem clockInternalWordOfFrame
    (w : Nat → Fin 8) (p : Nat)
    (h : followerPair (w p) (w (p + 1)) =
      (w p, w (p + 1))) :
    clockInternalWord w p = w := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [clockInternalWord, hx, hy, clockWriteSelf]

/-- Inside prefix: a B/DONE,B/DONE edge is the
    identity on the entire word, not merely on the potential. -/
theorem clockInternalInsideWord
    (w : Nat → Fin 8) (n k p : Nat)
    (hfirst : firstNonDone w n 0 = k)
    (hp : p + 1 < k) :
    clockInternalWord w p = w := by
  apply clockInternalWordOfFrame
  exact clockFollowerDonePair w n p (by
    rw [hfirst]
    exact hp)

/-- Inside-prefix framing for any root certificate. -/
theorem clockInternalInsidePsi
    (w : Nat → Fin 8) (n k p : Nat) (cert : SerCert)
    (hfirst : firstNonDone w n 0 = k)
    (hp : p + 1 < k) :
    startPsiWord n cert (clockInternalWord w p) =
      startPsiWord n cert w := by
  rw [clockInternalInsideWord w n k p hfirst hp]

/-- Far suffix: both the frontier and the potential
    are unchanged by a source offset p >= k+3. -/
theorem clockInternalFarFrame
    (w : Nat → Fin 8) (n k p : Nat) (cert : SerCert)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hp : k + 2 < p) :
    firstNonDone (clockInternalWord w p) n 0 = k ∧
    startPsiWord n cert (clockInternalWord w p) =
      startPsiWord n cert w := by
  have hlocal :
      ∀ i, i ≤ k + 2 → w i = clockInternalWord w p i := by
    intro i hi
    exact (clockInternalWordRemote w p i
      (by omega) (by omega)).symm
  constructor
  · apply clockFirstNonDoneStablePrefix w (clockInternalWord w p)
      n k hk hfirst
    intro i hi
    exact hlocal i (by omega)
  · exact (clockPsiWordLocality n cert w (clockInternalWord w p)
      k hk hfirst hlocal).symm

/-- The first unfinished index advances by exactly one if and
    only if the source becomes DONE and the responder is non-DONE.
    This is the local direction used by the B/WAIT observation rows. -/
theorem clockInternalAdvanceFrontier
    (w : Nat → Fin 8) (n k : Nat)
    (hnext : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hdone : (clockInternalWord w k k).val = 6)
    (hnew : (clockInternalWord w k (k + 1)).val ≠ 6) :
    firstNonDone (clockInternalWord w k) n 0 = k + 1 := by
  let v := clockInternalWord w k
  have hp : ∀ i, i < k + 1 → (v i).val = 6 := by
    intro i hi
    by_cases he : i = k
    · subst i
      exact hdone
    · have hi : i < k := by omega
      have hf : v i = w i :=
        clockInternalWordRemote w k i (by omega) (by omega)
      rw [hf]
      exact clockFirstNonDonePrefixDone w n 0 i
        (by omega) (by
          rw [hfirst]
          exact hi)
  have hr := clockFirstNonDoneAt v n 0 (k + 1) hnext
    (by
      intro i hi
      simpa only [Nat.zero_add] using hp i hi)
    (by simpa only [Nat.zero_add] using hnew)
  simpa only [Nat.zero_add] using hr

/-- Lift a strict window comparison into the real firstNonDone
    word. All prefix and suffix facts are discharged once. -/
theorem clockInternalAdvanceStrictOfWindow
    (w : Nat → Fin 8) (n k : Nat)
    (hpositive : 0 < k)
    (hnext : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hdone : (clockInternalWord w k k).val = 6)
    (hfront : (clockInternalWord w k (k + 1)).val ≠ 6)
    (hwindow :
      clockWindowRemainder n (k + 1)
        (clockInternalWord w k (k + 1))
        (w (k + 2)) (w (k + 3)) + 1 ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2))) :
    startPsiWord n .RUNNING (clockInternalWord w k) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockInternalWord w k
  have hfrontV : firstNonDone v n 0 = k + 1 :=
    clockInternalAdvanceFrontier w n k hnext hfirst hdone hfront
  have hroot : (w 0).val = 6 :=
    clockFirstNonDonePrefixDone w n 0 0 (by omega) (by
      rw [hfirst]
      exact hpositive)
  have hrootV : (v 0).val = 6 := by
    have hh : v 0 = w 0 :=
      clockInternalWordRemote w k 0
        (by omega) (by omega)
    rw [hh]
    exact hroot
  have hw :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by omega
  have hv :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by omega
  have hsecond : v (k + 2) = w (k + 2) :=
    clockInternalWordRemote w k (k + 2) (by omega) (by omega)
  have hthird : v (k + 3) = w (k + 3) :=
    clockInternalWordRemote w k (k + 3) (by omega) (by omega)
  have hbefore := clockPsiRunningWindow n k w hw hfirst
  have hafter := clockPsiRunningWindow n (k + 1) v hv hfrontV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore, hsecond, hthird]
  exact hwindow

/-- The B/WAIT + INTERNAL_OK row advances the
    first non-DONE offset and strictly reduces the full word's Psi. -/
theorem clockInternalWaitInternalWordStrict
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n)
    (hpositive : 0 < k)
    (hnext : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hy : w (k + 1) = (2 : Fin 8)) :
    startPsiWord n .RUNNING (clockInternalWord w k) + 1 ≤
      startPsiWord n .RUNNING w := by
  have hpair : followerPair (w k) (w (k + 1)) =
      ((6 : Fin 8), (4 : Fin 8)) := by
    rw [hx, hy]
    rfl
  apply clockInternalAdvanceStrictOfWindow
    w n k hpositive hnext hfirst
  · rw [clockInternalWordSource, hpair]
    decide
  · rw [clockInternalWordTarget, hpair]
    decide
  · rw [clockInternalWordTarget, hpair, hx, hy]
    exact clockWindowWaitInternalStrict n k
      (w (k + 2)) (w (k + 3)) hn hnext

/-- B/WAIT + LEAF_OK makes the responder F, advances
    the frontier, and strictly reduces the full word's Psi. -/
theorem clockInternalWaitLeafWordStrict
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n)
    (hpositive : 0 < k)
    (hnext : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hy : w (k + 1) = (3 : Fin 8)) :
    startPsiWord n .RUNNING (clockInternalWord w k) + 1 ≤
      startPsiWord n .RUNNING w := by
  have hpair : followerPair (w k) (w (k + 1)) =
      ((6 : Fin 8), (7 : Fin 8)) := by
    rw [hx, hy]
    rfl
  apply clockInternalAdvanceStrictOfWindow
    w n k hpositive hnext hfirst
  · rw [clockInternalWordSource, hpair]
    decide
  · rw [clockInternalWordTarget, hpair]
    decide
  · rw [clockInternalWordTarget, hpair, hx, hy]
    exact clockWindowWaitLeafStrict n k
      (w (k + 2)) (w (k + 3)) hn hnext

/-- Pure 8x8 mirror for the source shape's coarse high/low bit:
    serving source >= B/NEW never changes whether it is >= B/NEW. -/
theorem clockFollowerSourceHigh :
    ∀ x y : Fin 8,
      (4 ≤ (followerPair x y).1.val) ↔ (4 ≤ x.val) := by
  decide

/-- Psi depends on its third window shape only through this bit. -/
theorem clockWindowThirdHighCongr
    (n k : Nat) (x y z t : Fin 8)
    (hh : (4 ≤ z.val) ↔ (4 ≤ t.val)) :
    clockWindowRemainder n k x y z =
      clockWindowRemainder n k x y t := by
  by_cases hz : 4 ≤ z.val
  · have ht : 4 ≤ t.val := hh.mp hz
    simp [clockWindowRemainder, hz, ht]
  · have ht : ¬ 4 ≤ t.val := by
      intro h
      exact hz (hh.mpr h)
    simp [clockWindowRemainder, hz, ht]

/-- P=k+2: the source high/low bit cannot change,
    so the lookahead window remains exactly equal. -/
theorem clockInternalThirdLookaheadFrame
    (w : Nat → Fin 8) (n k : Nat) (cert : SerCert)
    (hk : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hnext : k + 3 < n) :
    firstNonDone (clockInternalWord w (k + 2)) n 0 = k ∧
    startPsiWord n cert (clockInternalWord w (k + 2)) =
      startPsiWord n cert w := by
  let v := clockInternalWord w (k + 2)
  have hfront : firstNonDone v n 0 = k := by
    apply clockFirstNonDoneStablePrefix w v n k hk hfirst
    intro i hi
    exact (clockInternalWordRemote w (k + 2) i
      (by omega) (by omega)).symm
  have hzero : v 0 = w 0 :=
    clockInternalWordRemote w (k + 2) 0 (by omega) (by omega)
  have hx : v k = w k :=
    clockInternalWordRemote w (k + 2) k (by omega) (by omega)
  have hy : v (k + 1) = w (k + 1) :=
    clockInternalWordRemote w (k + 2) (k + 1)
      (by omega) (by omega)
  have hz : (4 ≤ (v (k + 2)).val) ↔
      (4 ≤ (w (k + 2)).val) := by
    show (4 ≤ (clockInternalWord w (k + 2) (k + 2)).val) ↔ _
    rw [clockInternalWordSource]
    exact clockFollowerSourceHigh (w (k + 2)) (w (k + 3))
  constructor
  · exact hfront
  · cases cert with
    | IDLE =>
      rfl
    | REQUESTED =>
      rfl
    | RUNNING =>
      by_cases hr : (w 0).val ≤ 3 ∨ (w 0).val = 7
      · have hrV : (v 0).val ≤ 3 ∨ (v 0).val = 7 := by
          simpa only [hzero] using hr
        rw [clockPsiRunningNonB n v hrV,
          clockPsiRunningNonB n w hr]
      · have hrV :
            ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
          simpa only [hzero] using hr
        have hbefore := clockPsiRunningWindow n k w hr hfirst
        have hafter := clockPsiRunningWindow n k v hrV hfront
        change startPsiWord n .RUNNING v =
          startPsiWord n .RUNNING w
        rw [hafter, hbefore, hx, hy]
        exact clockWindowThirdHighCongr n k
          (w k) (w (k + 1)) (v (k + 2)) (w (k + 2)) hz

/-- A two-shape finite rank for the middle lookahead. The single
    leaf case is distinguished from the affine branch. -/
def clockMiddleRank (y z : Fin 8) : Nat :=
  if y.val = 3 then 0
  else if y.val = 2 then 3
  else if y.val = 1 then (if 4 ≤ z.val then 5 else 4)
  else 6

/-- Exact 8x8 finite mirror, checked by the kernel. -/
theorem clockMiddleRankMono :
    ∀ y z : Fin 8,
      clockMiddleRank (followerPair y z).1
        (followerPair y z).2 ≤ clockMiddleRank y z := by
  decide

/-- Serving the middle lookahead never creates or removes a
    LEAF_OK source: a C/LEAF_OK source remains C/LEAF_OK. -/
theorem clockMiddleLeafIff :
    ∀ y z : Fin 8,
      (followerPair y z).1.val = 3 ↔ y.val = 3 := by
  decide

/-- The bulk middle-lookahead row is either the short leaf ticket
    or a common affine baseline plus clockMiddleRank. -/
theorem clockWindowMiddleBulk
    (n k : Nat) (y z : Fin 8)
    (hn : 4 ≤ n) (hnext : k + 2 < n) :
    clockWindowRemainder n k 5 y z =
      if y.val = 3 then k + 4
      else 5 * n - 10 - 4 * k + clockMiddleRank y z := by
  have hk : k ≠ n := by omega
  have hl : k + 1 ≠ n := by omega
  have hp : k + 2 ≠ n := by omega
  by_cases hthree : y.val = 3
  · simp [clockWindowRemainder, clockMiddleRank,
      hk, hl, hp, hthree] <;> omega
  · by_cases hone : y.val = 1
    · by_cases hz : 4 ≤ z.val
      · simp [clockWindowRemainder, clockMiddleRank,
          hk, hl, hp, hthree, hone, hz] <;> omega
      · simp [clockWindowRemainder, clockMiddleRank,
          hk, hl, hp, hthree, hone, hz] <;> omega
    · by_cases htwo : y.val = 2
      · simp [clockWindowRemainder, clockMiddleRank,
          hk, hl, hp, hthree, hone, htwo] <;> omega
      · simp [clockWindowRemainder, clockMiddleRank,
          hk, hl, hp, hthree, hone, htwo] <;> omega

/-- Finite middle-window comparison for arbitrary
    old frontier shape and arbitrary responder/extra lookahead.
    No n-dependent enumeration is performed. -/
theorem clockWindowMiddleMono
    (n k : Nat) (x y z : Fin 8)
    (hn : 4 ≤ n) (hnext : k + 2 < n) :
    clockWindowRemainder n k x
        (followerPair y z).1 (followerPair y z).2 ≤
      clockWindowRemainder n k x y z := by
  by_cases hx : x = (5 : Fin 8)
  · subst x
    have hleaf := clockMiddleLeafIff y z
    rw [clockWindowMiddleBulk n k
          (followerPair y z).1 (followerPair y z).2 hn hnext,
        clockWindowMiddleBulk n k y z hn hnext]
    by_cases hy : y.val = 3
    · have hy' : (followerPair y z).1.val = 3 := hleaf.mpr hy
      simpa only [if_pos hy', if_pos hy] using
        (Nat.le_refl (k + 4))
    · have hy' : (followerPair y z).1.val ≠ 3 := by
        intro h
        exact hy (hleaf.mp h)
      simpa only [if_neg hy', if_neg hy] using
        (Nat.add_le_add_left (clockMiddleRankMono y z)
          (5 * n - 10 - 4 * k))
  · have hk : k ≠ n := by omega
    have hl : k + 1 ≠ n := by omega
    have hfive : x.val ≠ 5 := by
      intro h
      apply hx
      apply Fin.ext
      simpa using h
    simp [clockWindowRemainder, hk, hl, hfive]

/-- P=k+1: the nonterminal middle-lookahead
    update does not increase Psi. -/
theorem clockInternalMiddleLookaheadMono
    (w : Nat → Fin 8) (n k : Nat) (cert : SerCert)
    (hn : 4 ≤ n)
    (hnext : k + 2 < n)
    (hfirst : firstNonDone w n 0 = k) :
    firstNonDone (clockInternalWord w (k + 1)) n 0 = k ∧
    startPsiWord n cert (clockInternalWord w (k + 1)) ≤
      startPsiWord n cert w := by
  let v := clockInternalWord w (k + 1)
  have hk : k < n := by omega
  have hfront : firstNonDone v n 0 = k := by
    apply clockFirstNonDoneStablePrefix w v n k hk hfirst
    intro i hi
    exact (clockInternalWordRemote w (k + 1) i
      (by omega) (by omega)).symm
  have hzero : v 0 = w 0 :=
    clockInternalWordRemote w (k + 1) 0 (by omega) (by omega)
  have hx : v k = w k :=
    clockInternalWordRemote w (k + 1) k
      (by omega) (by omega)
  have hy : v (k + 1) =
      (followerPair (w (k + 1)) (w (k + 2))).1 :=
    clockInternalWordSource w (k + 1)
  have hz : v (k + 2) =
      (followerPair (w (k + 1)) (w (k + 2))).2 :=
    clockInternalWordTarget w (k + 1)
  constructor
  · exact hfront
  · cases cert with
    | IDLE =>
      exact Nat.le_refl _
    | REQUESTED =>
      exact Nat.le_refl _
    | RUNNING =>
      by_cases hr : (w 0).val ≤ 3 ∨ (w 0).val = 7
      · have hrV : (v 0).val ≤ 3 ∨ (v 0).val = 7 := by
          simpa only [hzero] using hr
        rw [clockPsiRunningNonB n v hrV,
          clockPsiRunningNonB n w hr]
        exact Nat.le_refl 3
      · have hrV :
            ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
          simpa only [hzero] using hr
        have hbefore := clockPsiRunningWindow n k w hr hfirst
        have hafter := clockPsiRunningWindow n k v hrV hfront
        change startPsiWord n .RUNNING v ≤
          startPsiWord n .RUNNING w
        rw [hafter, hbefore, hx, hy, hz]
        exact clockWindowMiddleMono n k
          (w k) (w (k + 1)) (w (k + 2)) hn hnext

/-- A closed literal counterexample to the premise that a
    non-DONE frontier can only stay at k or move to k+1:
    n=4, old word [B/DONE,B/DONE,F,C/NONE], INTERNAL edge p=1.
    The successor word is [B/DONE,F,F,C/NONE].
    Thus k=2 moves LEFT to k'=1; Psi strictly decreases 4 -> 3. -/
theorem clockLeftShiftWitness :
    let w : Nat → Fin 8 := fun i =>
      if i = 0 then 6
      else if i = 1 then 6
      else if i = 2 then 7
      else 0
    firstNonDone w 4 0 = 2 ∧
      firstNonDone (clockInternalWord w 1) 4 0 = 1 ∧
      startPsiWord 4 .RUNNING w = 4 ∧
      startPsiWord 4 .RUNNING (clockInternalWord w 1) = 3 := by
  decide

end L3


namespace L3

set_option autoImplicit false

/-!
This section proves the missing INTERNAL left-frontier and
central-frontier comparisons for all natural lengths n>=4.

The 8x8 finite lemma classifies B/DONE -> (C,F,B) at the
left frontier. For a C or F successor the new firstNonDone
moves from k to k-1, and the affine-window comparison is strict.
For a B successor the whole transition is an identity.

At the central frontier, C/F-source rows are weak frames,
B/NEW and the two B/WAIT admission rows are strict by the
earlier lemmas, B/WAIT+PENDING is a frame,
and B/WAIT+other is strictly decreasing. ROOT_OUT and
non-IDLE ROOT_IN remain unproved at this stage.
-/

/-- Closed, finite 8-shape classification at the left frontier. -/
theorem clockDoneLeftFinite :
    ∀ y : Fin 8,
      (y.val ≤ 3 →
        followerPair (6 : Fin 8) y =
          ((5 : Fin 8), (1 : Fin 8))) ∧
      (y.val = 7 →
        followerPair (6 : Fin 8) y =
          ((7 : Fin 8), (7 : Fin 8))) ∧
      ((y.val = 4 ∨ y.val = 5) →
        followerPair (6 : Fin 8) y = ((6 : Fin 8), y)) := by
  decide

/-- If a previously B/DONE source becomes non-DONE, the first
    unfinished position moves backward exactly one offset. -/
theorem clockInternalLeftFrontier
    (w : Nat → Fin 8) (n k : Nat)
    (hk : 0 < k) (hkn : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hnew :
      (clockInternalWord w (k - 1) (k - 1)).val ≠ 6) :
    firstNonDone (clockInternalWord w (k - 1)) n 0 =
      k - 1 := by
  have hpre :
      ∀ i, i < k - 1 →
        (clockInternalWord w (k - 1) i).val = 6 := by
    intro i hi
    have hremote : clockInternalWord w (k - 1) i = w i :=
      clockInternalWordRemote w (k - 1) i
        (by omega) (by omega)
    rw [hremote]
    exact clockFirstNonDonePrefixDone w n 0 i
      (by omega) (by
        rw [hfirst]
        omega)
  have hfound := clockFirstNonDoneAt
    (clockInternalWord w (k - 1)) n 0 (k - 1)
    (by omega)
    (by
      intro i hi
      simpa only [Nat.zero_add] using hpre i hi)
    (by simpa only [Nat.zero_add] using hnew)
  simpa only [Nat.zero_add] using hfound

/-- A C-frontier challenged from the previous B/DONE site
    decreases Psi by 1 or 2, including the last-site case. -/
theorem clockWindowLeftCStrict
    (n k : Nat) (x y z : Fin 8)
    (hn : 4 ≤ n) (hk : 0 < k) (hkn : k < n)
    (hx : x.val ≤ 3) :
    clockWindowRemainder n (k - 1) 5 1 y + 1 ≤
      clockWindowRemainder n k x y z := by
  have hp : k - 1 ≠ n := by omega
  have hc : k ≠ n := by omega
  have hpred : k - 1 + 1 ≠ n := by omega
  have hnoF : x.val ≠ 7 := by omega
  by_cases hlast : k + 1 = n
  · have hnewLast : k - 1 + 2 = n := by omega
    simp [clockWindowRemainder, hp, hc, hpred, hnoF,
      hx, hlast, hnewLast] <;> omega
  · have hnewLast : k - 1 + 2 ≠ n := by omega
    by_cases hy : 4 ≤ y.val
    · simp [clockWindowRemainder, hp, hc, hpred, hnoF,
        hx, hlast, hnewLast, hy] <;> omega
    · simp [clockWindowRemainder, hp, hc, hpred, hnoF,
        hx, hlast, hnewLast, hy] <;> omega

/-- B/DONE,F -> F,F moves the frontier left by one and
    decreases the F-ticket exactly by one. -/
theorem clockWindowLeftFStrict
    (n k : Nat) (y z : Fin 8)
    (hk : 0 < k) (hkn : k < n) :
    clockWindowRemainder n (k - 1) 7 7 y + 1 ≤
      clockWindowRemainder n k 7 y z := by
  have hp : k - 1 ≠ n := by omega
  have hc : k ≠ n := by omega
  simp [clockWindowRemainder, hp, hc] <;> omega

/-- Common word-level lift for the two left-shift rows. The
    window premise is only a comparison of three shape cells. -/
theorem clockInternalLeftStrictOfWindow
    (w : Nat → Fin 8) (n k : Nat)
    (hk : 2 ≤ k) (hkn : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hnew :
      (clockInternalWord w (k - 1) (k - 1)).val ≠ 6)
    (hwindow :
      clockWindowRemainder n (k - 1)
        (clockInternalWord w (k - 1) (k - 1))
        (clockInternalWord w (k - 1) k)
        (w (k + 1)) + 1 ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2))) :
    startPsiWord n .RUNNING
        (clockInternalWord w (k - 1)) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockInternalWord w (k - 1)
  have hfrontV : firstNonDone v n 0 = k - 1 :=
    clockInternalLeftFrontier w n k (by omega)
      hkn hfirst hnew
  have hwzero : (w 0).val = 6 :=
    clockFirstNonDonePrefixDone w n 0 0 (by omega)
      (by
        rw [hfirst]
        omega)
  have hvzero : (v 0).val = 6 := by
    change (clockInternalWord w (k - 1) 0).val = 6
    rw [clockInternalWordRemote w (k - 1) 0
      (by omega) (by omega)]
    exact hwzero
  have hrootW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by omega
  have hrootV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by omega
  have hindex : k - 1 + 1 = k := by omega
  have hlook : v (k - 1 + 2) = w (k + 1) := by
    have hidx : k - 1 + 2 = k + 1 := by omega
    rw [hidx]
    exact clockInternalWordRemote w (k - 1) (k + 1)
      (by omega) (by omega)
  have hbefore := clockPsiRunningWindow n k w hrootW hfirst
  have hafter := clockPsiRunningWindow n (k - 1) v
    hrootV hfrontV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore, hindex, hlook]
  exact hwindow

/-- Actual all-n C-source challenge at p=k-1. -/
theorem clockInternalLeftCWordStrict
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n) (hk : 2 ≤ k) (hkn : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hc : (w k).val ≤ 3) :
    startPsiWord n .RUNNING
        (clockInternalWord w (k - 1)) + 1 ≤
      startPsiWord n .RUNNING w := by
  have hprev : w (k - 1) = (6 : Fin 8) := by
    apply Fin.ext
    change (w (k - 1)).val = 6
    exact clockFirstNonDonePrefixDone w n 0 (k - 1)
      (by omega) (by
        rw [hfirst]
        omega)
  have hpair :
      followerPair (w (k - 1)) (w k) =
        ((5 : Fin 8), (1 : Fin 8)) := by
    rw [hprev]
    exact (clockDoneLeftFinite (w k)).1 hc
  have hsource :
      clockInternalWord w (k - 1) (k - 1) =
        (5 : Fin 8) := by
    rw [clockInternalWordSource,
      show k - 1 + 1 = k from by omega, hpair]
  have htarget :
      clockInternalWord w (k - 1) k = (1 : Fin 8) := by
    have heq : k - 1 + 1 = k := by omega
    have ht := clockInternalWordTarget w (k - 1)
    rw [heq, hpair] at ht
    exact ht
  apply clockInternalLeftStrictOfWindow
    w n k hk hkn hfirst
  · rw [hsource]
    decide
  · rw [hsource, htarget]
    exact clockWindowLeftCStrict
      n k (w k) (w (k + 1)) (w (k + 2))
      hn (by omega) hkn hc

/-- Actual all-n returning F row at p=k-1. -/
theorem clockInternalLeftFWordStrict
    (w : Nat → Fin 8) (n k : Nat)
    (hk : 2 ≤ k) (hkn : k < n)
    (hfirst : firstNonDone w n 0 = k)
    (hf : w k = (7 : Fin 8)) :
    startPsiWord n .RUNNING
        (clockInternalWord w (k - 1)) + 1 ≤
      startPsiWord n .RUNNING w := by
  have hprev : w (k - 1) = (6 : Fin 8) := by
    apply Fin.ext
    change (w (k - 1)).val = 6
    exact clockFirstNonDonePrefixDone w n 0 (k - 1)
      (by omega) (by
        rw [hfirst]
        omega)
  have hpair :
      followerPair (w (k - 1)) (w k) =
        ((7 : Fin 8), (7 : Fin 8)) := by
    rw [hprev, hf]
    exact (clockDoneLeftFinite (7 : Fin 8)).2.1 (by decide)
  have hsource :
      clockInternalWord w (k - 1) (k - 1) =
        (7 : Fin 8) := by
    rw [clockInternalWordSource,
      show k - 1 + 1 = k from by omega, hpair]
  have htarget :
      clockInternalWord w (k - 1) k = (7 : Fin 8) := by
    have heq : k - 1 + 1 = k := by omega
    have ht := clockInternalWordTarget w (k - 1)
    rw [heq, hpair] at ht
    exact ht
  apply clockInternalLeftStrictOfWindow
    w n k hk hkn hfirst
  · rw [hsource]
    decide
  · rw [hsource, htarget, hf]
    exact clockWindowLeftFStrict
      n k (w (k + 1)) (w (k + 2)) (by omega) hkn

/-- All internal predecessor edges are monotone
    for all three root certificates. The two actual retreat/
    challenge rows are strict under RUNNING. -/
theorem clockInternalLeftMono
    (w : Nat → Fin 8) (n k : Nat) (cert : SerCert)
    (hn : 4 ≤ n) (hk : 2 ≤ k) (hkn : k < n)
    (hfirst : firstNonDone w n 0 = k) :
    startPsiWord n cert (clockInternalWord w (k - 1)) ≤
      startPsiWord n cert w := by
  cases cert with
  | IDLE =>
    simp [startPsiWord]
  | REQUESTED =>
    simp [startPsiWord]
  | RUNNING =>
    have hprev : w (k - 1) = (6 : Fin 8) := by
      apply Fin.ext
      change (w (k - 1)).val = 6
      exact clockFirstNonDonePrefixDone w n 0 (k - 1)
        (by omega) (by
          rw [hfirst]
          omega)
    have hnotdone : (w k).val ≠ 6 := by
      have hb : firstNonDone w n 0 < 0 + n := by
        rw [hfirst]
        omega
      have h := clockFirstNonDoneFrontNotDone w n 0 hb
      rw [hfirst] at h
      exact h
    by_cases hc : (w k).val ≤ 3
    · have hdec := clockInternalLeftCWordStrict
        w n k hn hk hkn hfirst hc
      omega
    · by_cases hf : (w k).val = 7
      · have hshape : w k = (7 : Fin 8) := by
          apply Fin.ext
          simpa only [clockFinValSeven] using hf
        have hdec := clockInternalLeftFWordStrict
          w n k hk hkn hfirst hshape
        omega
      · have hband : (w k).val = 4 ∨ (w k).val = 5 := by
          have hlt := (w k).isLt
          omega
        have hframe :
            followerPair (w (k - 1)) (w k) =
              (w (k - 1), w k) := by
          rw [hprev]
          exact (clockDoneLeftFinite (w k)).2.2 hband
        have hh := clockInternalWordOfFrame w (k - 1) (by
          rw [show k - 1 + 1 = k from by omega]
          exact hframe)
        simpa only [hh] using
          (Nat.le_refl (startPsiWord n .RUNNING w))

/-- Closed 8x8 source tests for central-frontier C and F rows. -/
theorem clockCentralCFinite :
    ∀ x y : Fin 8,
      x.val ≤ 3 → (followerPair x y).1.val ≤ 3 := by
  decide

theorem clockCentralFFinite :
    ∀ y : Fin 8,
      (followerPair (7 : Fin 8) y).1 = (7 : Fin 8) := by
  decide

/-- Word-level central-frontier lift of an arbitrary window
    comparison. The root shape and lookahead at k+2 frame exactly. -/
theorem clockInternalCentralBound
    (w : Nat → Fin 8) (n k ticket : Nat)
    (hk : 0 < k) (hkn : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hsource : (clockInternalWord w k k).val ≠ 6)
    (hwindow :
      clockWindowRemainder n k
        (clockInternalWord w k k)
        (clockInternalWord w k (k + 1))
        (w (k + 2)) + ticket ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2))) :
    startPsiWord n .RUNNING (clockInternalWord w k) +
        ticket ≤ startPsiWord n .RUNNING w := by
  let v := clockInternalWord w k
  have hfirstV : firstNonDone v n 0 = k :=
    clockInternalFrontierStable n k w (by omega)
      hfirst hsource
  have hwzero : (w 0).val = 6 :=
    clockFirstNonDonePrefixDone w n 0 0 (by omega)
      (by
        rw [hfirst]
        omega)
  have hvzero : (v 0).val = 6 := by
    change (clockInternalWord w k 0).val = 6
    rw [clockInternalWordRemote w k 0
      (by omega) (by omega)]
    exact hwzero
  have hrW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by omega
  have hrV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by omega
  have hlook : v (k + 2) = w (k + 2) :=
    clockInternalWordRemote w k (k + 2)
      (by omega) (by omega)
  have hbefore := clockPsiRunningWindow n k w hrW hfirst
  have hafter := clockPsiRunningWindow n k v hrV hfirstV
  change startPsiWord n .RUNNING v + ticket ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore, hlook]
  exact hwindow

/-- An arbitrary C shape at the first non-DONE offset cannot
    change its window cost when serving the outgoing edge. -/
theorem clockInternalCentralCMono
    (w : Nat → Fin 8) (n k : Nat)
    (hk : 0 < k) (hkn : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hc : (w k).val ≤ 3) :
    startPsiWord n .RUNNING (clockInternalWord w k) ≤
      startPsiWord n .RUNNING w := by
  have hvC : (clockInternalWord w k k).val ≤ 3 := by
    rw [clockInternalWordSource]
    exact clockCentralCFinite (w k) (w (k + 1)) hc
  have hvF : (clockInternalWord w k k).val ≠ 7 := by omega
  have hwF : (w k).val ≠ 7 := by omega
  have hwindow :
      clockWindowRemainder n k
        (clockInternalWord w k k)
        (clockInternalWord w k (k + 1)) (w (k + 2)) + 0 ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2)) := by
    simp [clockWindowRemainder, hvC, hc, hvF, hwF]
  have hbound := clockInternalCentralBound
    w n k 0 hk hkn hfirst (by omega) hwindow
  simpa only [Nat.add_zero] using hbound

/-- Returning F at the central frontier retains the F ticket
    regardless of the responder shape. -/
theorem clockInternalCentralFMono
    (w : Nat → Fin 8) (n k : Nat)
    (hk : 0 < k) (hkn : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hf : w k = (7 : Fin 8)) :
    startPsiWord n .RUNNING (clockInternalWord w k) ≤
      startPsiWord n .RUNNING w := by
  have hsrc :
      clockInternalWord w k k = (7 : Fin 8) := by
    rw [clockInternalWordSource, hf]
    exact clockCentralFFinite (w (k + 1))
  have hwindow :
      clockWindowRemainder n k
        (clockInternalWord w k k)
        (clockInternalWord w k (k + 1)) (w (k + 2)) + 0 ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2)) := by
    rw [hsrc, hf]
    simp [clockWindowRemainder]
  have hnot : (clockInternalWord w k k).val ≠ 6 := by
    rw [hsrc]
    decide
  have hbound := clockInternalCentralBound
    w n k 0 hk hkn hfirst hnot hwindow
  simpa only [Nat.add_zero] using hbound

/-- B/WAIT encountering any responder other than PENDING,
    INTERNAL_OK or LEAF_OK creates (B/WAIT,PENDING), and the
    full-word potential decreases strictly. -/
theorem clockInternalCentralWaitOtherStrict
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n) (hk : 0 < k) (hkn : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hp : (w (k + 1)).val ≠ 1)
    (hi : (w (k + 1)).val ≠ 2)
    (hl : (w (k + 1)).val ≠ 3) :
    startPsiWord n .RUNNING (clockInternalWord w k) + 1 ≤
      startPsiWord n .RUNNING w := by
  have hpair :
      followerPair (w k) (w (k + 1)) =
        ((5 : Fin 8), (1 : Fin 8)) := by
    rw [hx]
    simp [followerPair, hp, hi, hl]
  have hsrc :
      clockInternalWord w k k = (5 : Fin 8) := by
    rw [clockInternalWordSource, hpair]
  have htgt :
      clockInternalWord w k (k + 1) = (1 : Fin 8) := by
    rw [clockInternalWordTarget, hpair]
  have hwindow :
      clockWindowRemainder n k
        (clockInternalWord w k k)
        (clockInternalWord w k (k + 1)) (w (k + 2)) + 1 ≤
      clockWindowRemainder n k
        (w k) (w (k + 1)) (w (k + 2)) := by
    rw [hsrc, htgt, hx]
    exact clockWindowWaitOtherStrict n k (w (k + 1))
      (w (k + 2)) hn hkn hp hi hl
  apply clockInternalCentralBound w n k 1 hk hkn hfirst
  · rw [hsrc]
    decide
  · exact hwindow

/-- The complete INTERNAL source-at-frontier class
    for k>=1 and k+1<n, with no hypothesis on the suffix. -/
theorem clockInternalCentralMono
    (w : Nat → Fin 8) (n k : Nat) (cert : SerCert)
    (hn : 4 ≤ n) (hk : 0 < k) (hkn : k + 1 < n)
    (hfirst : firstNonDone w n 0 = k) :
    startPsiWord n cert (clockInternalWord w k) ≤
      startPsiWord n cert w := by
  cases cert with
  | IDLE =>
    simp [startPsiWord]
  | REQUESTED =>
    simp [startPsiWord]
  | RUNNING =>
    have hnot : (w k).val ≠ 6 := by
      have hb : firstNonDone w n 0 < 0 + n := by
        rw [hfirst]
        omega
      have hh := clockFirstNonDoneFrontNotDone w n 0 hb
      rw [hfirst] at hh
      exact hh
    by_cases hc : (w k).val ≤ 3
    · exact clockInternalCentralCMono
        w n k hk hkn hfirst hc
    · by_cases hf : (w k).val = 7
      · have hshape : w k = (7 : Fin 8) := by
          apply Fin.ext
          simpa only [clockFinValSeven] using hf
        exact clockInternalCentralFMono
          w n k hk hkn hfirst hshape
      · by_cases hnShape : (w k).val = 4
        · have hshape : w k = (4 : Fin 8) := by
            apply Fin.ext
            simpa only [clockFinValFour] using hnShape
          have hh := clockInternalFrontierFreshStrict
            n k w hn hk hkn hfirst hshape
          omega
        · have hfive : (w k).val = 5 := by
            have hlt := (w k).isLt
            omega
          have hshape : w k = (5 : Fin 8) := by
            apply Fin.ext
            simpa only [clockFinValFive] using hfive
          by_cases hp : w (k + 1) = (1 : Fin 8)
          · have hframe :
                followerPair (w k) (w (k + 1)) =
                  (w k, w (k + 1)) := by
              rw [hshape, hp]
              decide
            have hh := clockInternalWordOfFrame w k hframe
            simpa only [hh] using
              (Nat.le_refl (startPsiWord n .RUNNING w))
          · by_cases hi : w (k + 1) = (2 : Fin 8)
            · have hh := clockInternalWaitInternalWordStrict
                w n k hn hk hkn hfirst hshape hi
              omega
            · by_cases hl : w (k + 1) = (3 : Fin 8)
              · have hh := clockInternalWaitLeafWordStrict
                  w n k hn hk hkn hfirst hshape hl
                omega
              · have hpVal : (w (k + 1)).val ≠ 1 := by
                  intro hv
                  apply hp
                  apply Fin.ext
                  simpa only [clockFinValOne] using hv
                have hiVal : (w (k + 1)).val ≠ 2 := by
                  intro hv
                  apply hi
                  apply Fin.ext
                  simpa only [clockFinValTwo] using hv
                have hlVal : (w (k + 1)).val ≠ 3 := by
                  intro hv
                  apply hl
                  apply Fin.ext
                  simpa only [clockFinValThree] using hv
                have hh := clockInternalCentralWaitOtherStrict
                  w n k hn hk hkn hfirst hshape
                  hpVal hiVal hlVal
                omega

/-- ROOT_IN at a non-IDLE root cannot disturb a previously
    REQUESTED root's ticket; the root certificate is unchanged. -/
theorem clockIncomingRequestedFrame
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hr : r.cert = .REQUESTED) :
    clockAbstractPsi n
      (rootIn (w (n - 1)) r).2
      (clockWrite w (n - 1)
        (rootIn (w (n - 1)) r).1) =
    clockAbstractPsi n r w := by
  have hcert : (rootIn (w (n - 1)) r).2.cert = .REQUESTED := by
    simp [rootIn, hr]
    repeat' split
    all_goals exact hr
  simp [clockAbstractPsi, startPsiWord, hcert, hr]

end L3


namespace L3

set_option autoImplicit false

/-!
All-n ROOT_OUT row arithmetic, and the early
ROOT_IN rows.

No result for the RUNNING completedB incoming seam, no assembled
three-kind monotonicity, and no expectation theorem is claimed.
-/

/-- The root window in RUNNING B phase is the already established
    affine remainder, with no assumption on the entire suffix. -/
private theorem clockRootRunningRemainder
    (n k : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hc : r.cert = .RUNNING) (hs : r.stage ≠ .nonB)
    (hf : firstNonDone (clockAbstractWord r w) n 0 = k) :
    clockAbstractPsi n r w =
      clockWindowRemainder n k
        (clockAbstractWord r w k)
        (clockAbstractWord r w (k + 1))
        (clockAbstractWord r w (k + 2)) := by
  rw [clockAbstractWindowAffine n k r w hc hs hf]
  exact (clockWindowAffine n k
    (clockAbstractWord r w k)
    (clockAbstractWord r w (k + 1))
    (clockAbstractWord r w (k + 2))).symm

/-- An RUNNING root at B/NEW always has first unfinished offset
    zero, and its entire word potential has this window value. -/
theorem clockRootFreshRemainder
    (n : Nat) (w : Nat → Fin 8) (hn : 0 < n) :
    clockAbstractPsi n
      { cert := .RUNNING, stage := .freshB } w =
      clockWindowRemainder n 0 4 (w 1) (w 2) := by
  have hf :
      firstNonDone (clockAbstractWord
        ({ cert := .RUNNING, stage := .freshB } : RootClass)
        w) n 0 = 0 := by
    apply clockFirstNonDoneAt _ n 0 0 (by omega)
    · intro i hi
      omega
    · simp [clockAbstractWord, clockRootShape]
  have hr := clockRootRunningRemainder n 0
    ({ cert := .RUNNING, stage := .freshB } : RootClass)
    w rfl (by decide) hf
  simpa [clockAbstractWord, clockRootShape] using hr

/-- A RUNNING B/WAIT root similarly has first unfinished
    offset zero. -/
theorem clockRootWaitRemainder
    (n : Nat) (w : Nat → Fin 8) (hn : 0 < n) :
    clockAbstractPsi n
      { cert := .RUNNING, stage := .waitingB } w =
      clockWindowRemainder n 0 5 (w 1) (w 2) := by
  have hf :
      firstNonDone (clockAbstractWord
        ({ cert := .RUNNING, stage := .waitingB } : RootClass)
        w) n 0 = 0 := by
    apply clockFirstNonDoneAt _ n 0 0 (by omega)
    · intro i hi
      omega
    · simp [clockAbstractWord, clockRootShape]
  have hr := clockRootRunningRemainder n 0
    ({ cert := .RUNNING, stage := .waitingB } : RootClass)
    w rfl (by decide) hf
  simpa [clockAbstractWord, clockRootShape] using hr

/-- A RUNNING B/DONE root whose child is not B/DONE has
    first unfinished offset one. -/
theorem clockRootCompletedRemainder
    (n : Nat) (w : Nat → Fin 8)
    (hn : 1 < n) (hy : (w 1).val ≠ 6) :
    clockAbstractPsi n
      { cert := .RUNNING, stage := .completedB } w =
      clockWindowRemainder n 1 (w 1) (w 2) (w 3) := by
  have hf :
      firstNonDone (clockAbstractWord
        ({ cert := .RUNNING, stage := .completedB } : RootClass)
        w) n 0 = 1 := by
    apply clockFirstNonDoneAt _ n 0 1 (by omega)
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp [clockAbstractWord, clockRootShape]
    · simpa [clockAbstractWord, clockRootShape] using hy
  have hr := clockRootRunningRemainder n 1
    ({ cert := .RUNNING, stage := .completedB } : RootClass)
    w rfl (by decide) hf
  simpa [clockAbstractWord, clockRootShape] using hr

/-- Single-cell writes used for each root-seam local row. -/
theorem clockWriteAtSite
    (w : Nat → Fin 8) (p : Nat) (x : Fin 8) :
    clockWrite w p x p = x := by
  simp [clockWrite]

theorem clockWriteOtherSite
    (w : Nat → Fin 8) (p i : Nat) (x : Fin 8)
    (hi : i ≠ p) :
    clockWrite w p x i = w i := by
  simp [clockWrite, hi]

/-- Source-root B/NEW / S2R challenge is strict in the entire
    abstract word, for every follower suffix. -/
theorem clockRootFreshChallengeStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB }
        (clockWrite w 1 1) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .freshB } w := by
  rw [clockRootWaitRemainder n (clockWrite w 1 1) (by omega),
    clockRootFreshRemainder n w (by omega)]
  rw [clockWriteAtSite, clockWriteOtherSite w 1 2 1 (by omega)]
  exact clockWindowFreshStrict n 0 (w 1) (w 2)
    hn (by omega)

/-- S2R B/WAIT observing INTERNAL_OK advances to B/DONE and
    makes a B/NEW child at offset one. -/
theorem clockRootWaitInternalStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hy : w 1 = (2 : Fin 8)) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .completedB }
        (clockWrite w 1 4) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB } w := by
  have hfront : ((clockWrite w 1 4) 1).val ≠ 6 := by
    rw [clockWriteAtSite]
    decide
  rw [clockRootCompletedRemainder n (clockWrite w 1 4)
      (by omega) hfront,
    clockRootWaitRemainder n w (by omega)]
  rw [clockWriteAtSite,
    clockWriteOtherSite w 1 2 4 (by omega),
    clockWriteOtherSite w 1 3 4 (by omega), hy]
  exact clockWindowWaitInternalStrict n 0 (w 2) (w 3)
    hn (by omega)

/-- S2R B/WAIT observing LEAF_OK advances to B/DONE and
    makes an F child at offset one. -/
theorem clockRootWaitLeafStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hy : w 1 = (3 : Fin 8)) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .completedB }
        (clockWrite w 1 7) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB } w := by
  have hfront : ((clockWrite w 1 7) 1).val ≠ 6 := by
    rw [clockWriteAtSite]
    decide
  rw [clockRootCompletedRemainder n (clockWrite w 1 7)
      (by omega) hfront,
    clockRootWaitRemainder n w (by omega)]
  rw [clockWriteAtSite,
    clockWriteOtherSite w 1 2 7 (by omega),
    clockWriteOtherSite w 1 3 7 (by omega), hy]
  exact clockWindowWaitLeafStrict n 0 (w 2) (w 3)
    hn (by omega)

/-- S2R B/WAIT with any other non-PENDING, non-OK child
    challenges that child, strictly decreasing Psi. -/
theorem clockRootWaitOtherStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hp : (w 1).val ≠ 1)
    (hi : (w 1).val ≠ 2)
    (hl : (w 1).val ≠ 3) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB }
        (clockWrite w 1 1) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB } w := by
  rw [clockRootWaitRemainder n (clockWrite w 1 1)
      (by omega), clockRootWaitRemainder n w (by omega)]
  rw [clockWriteAtSite, clockWriteOtherSite w 1 2 1 (by omega)]
  exact clockWindowWaitOtherStrict n 0 (w 1) (w 2)
    hn (by omega) hp hi hl

/-- S2R B/DONE with a C child issues an initial challenge at
    offset zero; this is the k=1 to k=0 seam version of the
    left-frontier C strict inequality. -/
theorem clockRootCompletedCStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hy : (w 1).val ≤ 3) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB }
        (clockWrite w 1 1) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .completedB } w := by
  have hfront : (w 1).val ≠ 6 := by omega
  rw [clockRootWaitRemainder n (clockWrite w 1 1)
      (by omega),
    clockRootCompletedRemainder n w (by omega) hfront]
  rw [clockWriteAtSite,
    clockWriteOtherSite w 1 2 1 (by omega)]
  exact clockWindowLeftCStrict n 1 (w 1) (w 2) (w 3)
    hn (by omega) (by omega) hy

/-- S6 at a completed root with F responder changes the root
    certificate to IDLE. The two exact tickets are 3 and 2. -/
theorem clockRootCompletedFinishStrict
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hy : w 1 = (7 : Fin 8)) :
    clockAbstractPsi n
        { cert := .IDLE, stage := .nonB } w + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .completedB } w := by
  have hfront : (w 1).val ≠ 6 := by
    rw [hy]
    decide
  rw [clockRootCompletedRemainder n w (by omega) hfront, hy]
  simp [clockAbstractPsi, clockWindowRemainder, startPsiWord]
  all_goals (split <;> omega)

/-- Option.some injectivity, expressed at the product fields. -/
private theorem clockSomePairFields
    {A B : Type} (a a' : A) (b b' : B)
    (h : (some (a, b) : Option (A × B)) = some (a', b')) :
    a = a' ∧ b = b' := by
  have hp := Option.some.inj h
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Finite certificate that every non-S1 ROOT_OUT step from an
    IDLE root leaves its root certificate IDLE. -/
theorem clockRootOutIdleCert (st : RootStage) :
    ∀ y : Fin 8,
      match rootOut { cert := .IDLE, stage := st } y with
      | none => True
      | some (r, _) => r.cert = .IDLE := by
  intro y
  have hb : (match rootOut { cert := .IDLE, stage := st } y with
      | none => true
      | some (r, _) => decide (r.cert = .IDLE)) = true := by
    revert y
    cases st <;> decide
  generalize rootOut { cert := .IDLE, stage := st } y = o at hb ⊢
  rcases o with _ | ⟨r, x⟩
  · trivial
  · exact of_decide_eq_true hb

/-- ROOT_OUT on an IDLE root frames Psi=2 for every row. -/
theorem clockRootOutIdleFrame
    (n : Nat) (st : RootStage) (w : Nat → Fin 8)
    (r' : RootClass) (y : Fin 8)
    (h : rootOut { cert := .IDLE, stage := st } (w 1) =
      some (r', y)) :
    clockAbstractPsi n r' (clockWrite w 1 y) =
      clockAbstractPsi n
        { cert := .IDLE, stage := st } w := by
  have hc := clockRootOutIdleCert st (w 1)
  rw [h] at hc
  simp [clockAbstractPsi, startPsiWord, hc]

/-- RUNNING nonB / recovery S_R: the root drops from 3 to
    the IDLE ticket 2, irrespective of its follower. -/
theorem clockRootOutNonBStrict
    (n : Nat) (w : Nat → Fin 8)
    (r' : RootClass) (y : Fin 8)
    (h : rootOut
      { cert := .RUNNING, stage := .nonB } (w 1) =
      some (r', y)) :
    clockAbstractPsi n r' (clockWrite w 1 y) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .nonB } w := by
  have hrow :
      rootOut
        { cert := .RUNNING, stage := .nonB } (w 1) =
        some ({ cert := .IDLE, stage := .waitingB }, (1 : Fin 8)) := rfl
  have hp := clockSomePairFields r'
    ({ cert := .IDLE, stage := .waitingB } : RootClass)
    y (1 : Fin 8) (h.symm.trans hrow)
  have hcert : r'.cert = .IDLE := by
    rw [hp.1]
  have hnew : clockAbstractPsi n r' (clockWrite w 1 y) = 2 := by
    simp [clockAbstractPsi, startPsiWord, hcert]
  have hold : clockAbstractPsi n
      { cert := .RUNNING, stage := .nonB } w = 3 := by
    simp [clockAbstractPsi, clockAbstractWord,
      clockRootShape, startPsiWord]
  omega

/-- ROOT_OUT monotonicity on all non-S1 rows at all n>=4.
    The case split is finite on root certificate/stage/child
    and invokes only the already proved all-n window inequalities. -/
theorem clockRootOutNonSOneMono
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8)
    (r' : RootClass) (y : Fin 8)
    (hreq : r.cert ≠ .REQUESTED)
    (h : rootOut r (w 1) = some (r', y)) :
    clockAbstractPsi n r' (clockWrite w 1 y) ≤
      clockAbstractPsi n r w := by
  cases r with
  | mk cert stage =>
    cases cert with
    | REQUESTED =>
      exact False.elim (hreq rfl)
    | IDLE =>
      exact Nat.le_of_eq (clockRootOutIdleFrame n stage w r' y h)
    | RUNNING =>
      cases stage with
      | nonB =>
        have hh := clockRootOutNonBStrict n w r' y h
        omega
      | freshB =>
        have hrow :
            rootOut
                { cert := .RUNNING, stage := .freshB } (w 1) =
              some ({ cert := .RUNNING, stage := .waitingB },
                (1 : Fin 8)) := rfl
        obtain ⟨hr, hy⟩ :=
          clockSomePairFields r'
            ({ cert := .RUNNING, stage := .waitingB } : RootClass)
            y (1 : Fin 8) (h.symm.trans hrow)
        rw [hr, hy]
        have hh := clockRootFreshChallengeStrict n w hn
        omega
      | waitingB =>
        by_cases hp : w 1 = (1 : Fin 8)
        · have hrow :
              rootOut
                  { cert := .RUNNING, stage := .waitingB } (w 1) =
                some ({ cert := .RUNNING, stage := .waitingB }, w 1) := by
            rw [hp]
            rfl
          obtain ⟨hr, hy⟩ :=
            clockSomePairFields r'
              ({ cert := .RUNNING, stage := .waitingB } : RootClass)
              y (w 1) (h.symm.trans hrow)
          rw [hr, hy, clockWriteSelf]
          exact Nat.le_refl _
        · by_cases hi : w 1 = (2 : Fin 8)
          · have hrow :
                rootOut
                    { cert := .RUNNING, stage := .waitingB } (w 1) =
                  some ({ cert := .RUNNING, stage := .completedB },
                    (4 : Fin 8)) := by
              rw [hi]
              rfl
            obtain ⟨hr, hy⟩ :=
              clockSomePairFields r'
                ({ cert := .RUNNING, stage := .completedB } : RootClass)
                y (4 : Fin 8) (h.symm.trans hrow)
            rw [hr, hy]
            have hh := clockRootWaitInternalStrict n w hn hi
            omega
          · by_cases hl : w 1 = (3 : Fin 8)
            · have hrow :
                  rootOut
                      { cert := .RUNNING, stage := .waitingB } (w 1) =
                    some ({ cert := .RUNNING, stage := .completedB },
                      (7 : Fin 8)) := by
                rw [hl]
                rfl
              obtain ⟨hr, hy⟩ :=
                clockSomePairFields r'
                  ({ cert := .RUNNING, stage := .completedB } : RootClass)
                  y (7 : Fin 8) (h.symm.trans hrow)
              rw [hr, hy]
              have hh := clockRootWaitLeafStrict n w hn hl
              omega
            · have hpv : (w 1).val ≠ 1 := by
                intro hv
                apply hp
                apply Fin.ext
                simpa only [clockFinValOne] using hv
              have hiv : (w 1).val ≠ 2 := by
                intro hv
                apply hi
                apply Fin.ext
                simpa only [clockFinValTwo] using hv
              have hlv : (w 1).val ≠ 3 := by
                intro hv
                apply hl
                apply Fin.ext
                simpa only [clockFinValThree] using hv
              have hrow :
                  rootOut
                      { cert := .RUNNING, stage := .waitingB } (w 1) =
                    some ({ cert := .RUNNING, stage := .waitingB },
                      (1 : Fin 8)) := by
                simp [rootOut, hpv, hiv, hlv]
              obtain ⟨hr, hy⟩ :=
                clockSomePairFields r'
                  ({ cert := .RUNNING, stage := .waitingB } : RootClass)
                  y (1 : Fin 8) (h.symm.trans hrow)
              rw [hr, hy]
              have hh := clockRootWaitOtherStrict n w hn hpv hiv hlv
              omega
      | completedB =>
        by_cases hf : w 1 = (7 : Fin 8)
        · have hrow :
              rootOut
                  { cert := .RUNNING, stage := .completedB } (w 1) =
                some ({ cert := .IDLE, stage := .nonB }, w 1) := by
            rw [hf]
            rfl
          obtain ⟨hr, hy⟩ :=
            clockSomePairFields r'
              ({ cert := .IDLE, stage := .nonB } : RootClass)
              y (w 1) (h.symm.trans hrow)
          rw [hr, hy]
          have hcert : clockAbstractPsi n
              { cert := .IDLE, stage := .nonB }
              (clockWrite w 1 (w 1)) =
              clockAbstractPsi n
                { cert := .IDLE, stage := .nonB } w := by
            rw [clockWriteSelf]
          rw [hcert]
          have hh := clockRootCompletedFinishStrict n w hn hf
          omega
        · by_cases hb : 4 ≤ (w 1).val
          · have hrow :
                rootOut
                    { cert := .RUNNING, stage := .completedB } (w 1) =
                  some ({ cert := .RUNNING, stage := .completedB },
                    w 1) := by
              simp [rootOut, hf, hb, show (w 1).val ≠ 7 from fun h => hf (Fin.ext h)]
            obtain ⟨hr, hy⟩ :=
              clockSomePairFields r'
                ({ cert := .RUNNING, stage := .completedB } : RootClass)
                y (w 1) (h.symm.trans hrow)
            rw [hr, hy, clockWriteSelf]
            exact Nat.le_refl _
          · have hc : (w 1).val ≤ 3 := by omega
            have hrow :
                rootOut
                    { cert := .RUNNING, stage := .completedB } (w 1) =
                  some ({ cert := .RUNNING, stage := .waitingB },
                    (1 : Fin 8)) := by
              simp [rootOut, hf, hb, show (w 1).val ≠ 7 from fun h => hf (Fin.ext h)]
            obtain ⟨hr, hy⟩ :=
              clockSomePairFields r'
                ({ cert := .RUNNING, stage := .waitingB } : RootClass)
                y (1 : Fin 8) (h.symm.trans hrow)
            rw [hr, hy]
            have hh := clockRootCompletedCStrict n w hn hc
            omega

/-- ROOT_IN never changes a non-IDLE root class: the incoming
    seam is a follower-only update. -/
theorem clockRootIncomingNonidleRootFrame
    (r : RootClass) (x : Fin 8)
    (hr : r.cert ≠ .IDLE) :
    (rootIn x r).2 = r := by
  simp [rootIn, hr]
  repeat' split
  all_goals rfl

/-- For a RUNNING non-B root, the incoming seam is invisible to
    Psi, independently of the incoming follower shape. -/
theorem clockIncomingRunningNonBFrame
    (n : Nat) (w : Nat → Fin 8) (x : Fin 8) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .nonB }
        (clockWrite w (n - 1) x) =
      clockAbstractPsi n
        { cert := .RUNNING, stage := .nonB } w := by
  simp [clockAbstractPsi, clockAbstractWord,
    clockRootShape, startPsiWord]

/-- The root-in seam at n-1 is strictly beyond both lookahead
    offsets 1 and 2 when n>=4. -/
theorem clockIncomingRunningFreshFrame
    (n : Nat) (w : Nat → Fin 8) (x : Fin 8)
    (hn : 4 ≤ n) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .freshB }
        (clockWrite w (n - 1) x) =
      clockAbstractPsi n
        { cert := .RUNNING, stage := .freshB } w := by
  rw [clockRootFreshRemainder n
      (clockWrite w (n - 1) x) (by omega),
    clockRootFreshRemainder n w (by omega)]
  rw [clockWriteOtherSite w (n - 1) 1 x (by omega),
    clockWriteOtherSite w (n - 1) 2 x (by omega)]

/-- Same frame for a RUNNING B/WAIT root. -/
theorem clockIncomingRunningWaitFrame
    (n : Nat) (w : Nat → Fin 8) (x : Fin 8)
    (hn : 4 ≤ n) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB }
        (clockWrite w (n - 1) x) =
      clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB } w := by
  rw [clockRootWaitRemainder n
      (clockWrite w (n - 1) x) (by omega),
    clockRootWaitRemainder n w (by omega)]
  rw [clockWriteOtherSite w (n - 1) 1 x (by omega),
    clockWriteOtherSite w (n - 1) 2 x (by omega)]

/-- The complete RUNNING ROOT_IN frames for stages nonB,
    freshB and waitingB. Only completedB remains, where the
    first unfinished offset can reach the last follower. -/
theorem clockIncomingRunningBeforeCompleted
    (n : Nat) (hn : 4 ≤ n) (st : RootStage)
    (w : Nat → Fin 8) (hs : st ≠ .completedB) :
    clockAbstractPsi n
      (rootIn (w (n - 1))
        { cert := .RUNNING, stage := st }).2
      (clockWrite w (n - 1)
        (rootIn (w (n - 1))
          { cert := .RUNNING, stage := st }).1) ≤
    clockAbstractPsi n
      { cert := .RUNNING, stage := st } w := by
  have hr :
      (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := st } : RootClass)).2 =
        { cert := .RUNNING, stage := st } :=
    clockRootIncomingNonidleRootFrame _ _ (fun h => SerCert.noConfusion h)
  rw [hr]
  cases st with
  | freshB =>
    have heq := clockIncomingRunningFreshFrame
      n w (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := .freshB } : RootClass)).1 hn
    omega
  | waitingB =>
    have heq := clockIncomingRunningWaitFrame
      n w (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := .waitingB } : RootClass)).1 hn
    omega
  | completedB =>
    exact False.elim (hs rfl)
  | nonB =>
    have heq := clockIncomingRunningNonBFrame
      n w (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := .nonB } : RootClass)).1
    omega

end L3


namespace L3

set_option autoImplicit false

/-!
The proof obligations
are the completedB ROOT_IN seam, three-kind abstract monotonicity,
then nominated strict decrease and physical drift.

The two structural lemmas are placed before the window inequalities:
an incoming last-site write either preserves k<n-1, or sets
the frontier to n-1 when the prior k was at or beyond n-1.
-/

def clockIncomingShape (x : Fin 8) : Fin 8 :=
  if x.val = 1 then 3
  else if 4 ≤ x.val ∧ x.val ≤ 6 then 0
  else x

/-- Exact eight-shape quotient of the real rootIn action. -/
theorem clockIncomingShapeLiteral :
    ∀ x : Fin 8,
      (rootIn x
        { cert := .RUNNING, stage := .completedB }).1 =
        clockIncomingShape x := by
  decide

/-- The seam never introduces a new B shape from a C/F shape. -/
theorem clockIncomingShapeHighWeak :
    ∀ x : Fin 8,
      4 ≤ (clockIncomingShape x).val → 4 ≤ x.val := by
  decide

/-- Every incoming seam response is non-B/DONE. -/
theorem clockIncomingShapeNotDone :
    ∀ x : Fin 8, (clockIncomingShape x).val ≠ 6 := by
  decide

def clockIncomingWord (n : Nat) (w : Nat → Fin 8) :
    Nat → Fin 8 :=
  clockWrite w (n - 1) (clockIncomingShape (w (n - 1)))

theorem clockIncomingWordAt (n : Nat) (w : Nat → Fin 8) :
    clockIncomingWord n w (n - 1) =
      clockIncomingShape (w (n - 1)) := by
  simp [clockIncomingWord, clockWrite]

theorem clockIncomingWordAway
    (n : Nat) (w : Nat → Fin 8) (i : Nat)
    (hi : i ≠ n - 1) :
    clockIncomingWord n w i = w i := by
  simp [clockIncomingWord, clockWrite, hi]

/-- The write at n-1 commutes with re-encoding a root-relative
    shape word because the root itself is at offset zero. -/
theorem clockAbstractWordWrite
    (r : RootClass) (w : Nat → Fin 8) (p : Nat)
    (x : Fin 8) (hp : 0 < p) :
    clockAbstractWord r (clockWrite w p x) =
      clockWrite (clockAbstractWord r w) p x := by
  funext i
  by_cases hi : i = 0
  · simp [clockAbstractWord, clockWrite, hi,
      show 0 ≠ p from by omega]
  · by_cases hj : i = p
    · have hp0 : p ≠ 0 := by omega
      subst i
      simp [clockAbstractWord, clockWrite, hp0]
    · simp [clockAbstractWord, clockWrite, hi, hj]

/-- A write at the final follower cannot change a first unfinished
    offset strictly before the final follower. -/
theorem clockIncomingFirstEarly
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n)
    (hk : k < n - 1)
    (hfirst : firstNonDone w n 0 = k) :
    firstNonDone (clockIncomingWord n w) n 0 = k := by
  apply clockFirstNonDoneStablePrefix w (clockIncomingWord n w)
    n k (by omega) hfirst
  intro i hi
  exact (clockIncomingWordAway n w i (by omega)).symm

/-- A write at the final follower that produces a non-DONE shape
    makes that last offset the frontier whenever the old frontier
    was at, or beyond, the last offset. Includes the all-DONE case. -/
theorem clockIncomingFirstLate
    (w : Nat → Fin 8) (n k : Nat)
    (hn : 4 ≤ n)
    (hk : n - 1 ≤ k)
    (hfirst : firstNonDone w n 0 = k)
    (hlast : (clockIncomingWord n w (n - 1)).val ≠ 6) :
    firstNonDone (clockIncomingWord n w) n 0 = n - 1 := by
  have hp : ∀ i, i < n - 1 →
      (clockIncomingWord n w i).val = 6 := by
    intro i hi
    have hremote : clockIncomingWord n w i = w i :=
      clockIncomingWordAway n w i (by omega)
    rw [hremote]
    exact clockFirstNonDonePrefixDone w n 0 i
      (by omega) (by
        rw [hfirst]
        omega)
  have hs := clockFirstNonDoneAt (clockIncomingWord n w)
    n 0 (n - 1) (by omega)
    (by
      intro i hi
      simpa only [Nat.zero_add] using hp i hi)
    (by simpa only [Nat.zero_add] using hlast)
  simpa only [Nat.zero_add] using hs

/-- Monotonicity in the high/low class of the third lookahead,
    for every n,k and without any terminal-case assumptions. -/
theorem clockWindowThirdWeak
    (n k : Nat) (x y z t : Fin 8)
    (hh : 4 ≤ t.val → 4 ≤ z.val) :
    clockWindowRemainder n k x y t ≤
      clockWindowRemainder n k x y z := by
  have htip :
      clockWindowTip n k x y t ≤
        clockWindowTip n k x y z := by
    by_cases hz : 4 ≤ z.val
    · by_cases ht : 4 ≤ t.val
      · simp [clockWindowTip, hz, ht]
      · by_cases hkn : k = n
        · simp [clockWindowTip, hkn]
        · by_cases hf : x.val = 7
          · simp [clockWindowTip, hkn, hf]
          · by_cases hc : x.val ≤ 3
            · simp [clockWindowTip, hkn, hf, hc]
            · by_cases hb : x.val = 4
              · simp [clockWindowTip, hkn, hf, hc, hb]
              · by_cases hw : x.val = 5
                · by_cases hl : k + 1 = n
                  · simp [clockWindowTip, hkn, hf, hc, hb, hw, hl]
                  · by_cases hp : y.val = 1
                    · by_cases he : k + 2 = n
                      · simp [clockWindowTip, hkn, hf, hc, hb, hw,
                          hl, hp, he]
                      · simp [clockWindowTip, hkn, hf, hc, hb, hw,
                          hl, hp, he, hz, ht] <;> omega
                    · simp [clockWindowTip, hkn, hf, hc, hb, hw,
                        hl, hp]
                · simp [clockWindowTip, hkn, hf, hc, hb, hw]
    · have ht : ¬ 4 ≤ t.val := by
        intro h
        exact hz (hh h)
      simp [clockWindowTip, hz, ht]
  rw [clockWindowAffine n k x y t,
    clockWindowAffine n k x y z]
  exact Nat.add_le_add_left htip (clockWindowLinear n k x y)

/-- When the frontier is n-2, the entire window remainder is
    n plus this finite 8x8 rank. The x=6 shape is unreachable
    at a genuine firstNonDone offset. -/
def clockNearEndRank (x y : Fin 8) : Nat :=
  if x.val = 7 then 0
  else if x.val ≤ 3 then 8
  else if x.val = 4 then 4
  else if x.val = 5 then
    if y.val = 1 then 3
    else if y.val = 2 then 6
    else if y.val = 3 then 2
    else 4
  else 0

/-- Closed 8x8 arithmetic certificate for a ROOT_IN update
    in the first lookahead of a frontier at offset n-2. -/
theorem clockNearEndRankIncomingWeak :
    ∀ x y : Fin 8,
      clockNearEndRank x (clockIncomingShape y) ≤
        clockNearEndRank x y := by
  decide

/-- Symbolic n-decomposition of the near-last window. -/
theorem clockNearEndWindow
    (n : Nat) (x y z : Fin 8)
    (hn : 4 ≤ n) (hx : x.val ≠ 6) :
    clockWindowRemainder n (n - 2) x y z =
      n + clockNearEndRank x y := by
  have hk : n - 2 ≠ n := by omega
  have hnext : n - 2 + 1 ≠ n := by omega
  have hlast : n - 2 + 2 = n := by omega
  by_cases hf : x.val = 7
  · simp [clockWindowRemainder, clockNearEndRank,
      hk, hnext, hlast, hf] <;> omega
  · by_cases hc : x.val ≤ 3
    · simp [clockWindowRemainder, clockNearEndRank,
        hk, hnext, hlast, hf, hc] <;> omega
    · by_cases hb : x.val = 4
      · simp [clockWindowRemainder, clockNearEndRank,
          hk, hnext, hlast, hf, hc, hb] <;> omega
      · by_cases hw : x.val = 5
        · by_cases hp : y.val = 1
          · simp [clockWindowRemainder, clockNearEndRank,
              hk, hnext, hlast, hf, hc, hb, hw, hp] <;> omega
          · by_cases hi : y.val = 2
            · simp [clockWindowRemainder, clockNearEndRank,
                hk, hnext, hlast, hf, hc, hb, hw,
                hp, hi] <;> omega
            · by_cases hl : y.val = 3
              · simp [clockWindowRemainder, clockNearEndRank,
                  hk, hnext, hlast, hf, hc, hb, hw,
                  hp, hi, hl] <;> omega
              · simp [clockWindowRemainder, clockNearEndRank,
                  hk, hnext, hlast, hf, hc, hb, hw,
                  hp, hi, hl] <;> omega
        · have hbad : False := by
            have hlt := x.isLt
            omega
          exact False.elim hbad

/-- At offset n-1 the window has only one relevant shape. -/
def clockLastRank (x : Fin 8) : Nat :=
  if x.val = 7 then 1
  else if x.val ≤ 3 then 4
  else if x.val = 4 ∨ x.val = 5 then 5
  else 0

/-- Closed eight-shape certificate at the last frontier.
    The assumption x != B/DONE excludes the all-DONE word. -/
theorem clockLastRankIncomingWeak :
    ∀ x : Fin 8,
      x.val ≠ 6 →
        clockLastRank (clockIncomingShape x) ≤
          clockLastRank x := by
  decide

/-- Symbolic decomposition of the last-frontier window. -/
theorem clockLastWindow
    (n : Nat) (x y z : Fin 8)
    (hn : 4 ≤ n) (hx : x.val ≠ 6) :
    clockWindowRemainder n (n - 1) x y z =
      n + clockLastRank x := by
  have hk : n - 1 ≠ n := by omega
  have hlast : n - 1 + 1 = n := by omega
  by_cases hf : x.val = 7
  · simp [clockWindowRemainder, clockLastRank,
      hk, hlast, hf] <;> omega
  · by_cases hc : x.val ≤ 3
    · simp [clockWindowRemainder, clockLastRank,
        hk, hlast, hf, hc] <;> omega
    · by_cases hb : x.val = 4
      · simp [clockWindowRemainder, clockLastRank,
          hk, hlast, hf, hc, hb] <;> omega
      · by_cases hw : x.val = 5
        · simp [clockWindowRemainder, clockLastRank,
            hk, hlast, hf, hc, hb, hw] <;> omega
        · have hbad : False := by
            have hlt := x.isLt
            omega
          exact False.elim hbad

/-- Both all-DONE terminal rows have exact n+c windows.
    ROOT_IN converts the final B/DONE to C/NONE, dropping one. -/
theorem clockIncomingAllDoneWindow
    (n : Nat) (y z : Fin 8) (hn : 4 ≤ n) :
    clockWindowRemainder n (n - 1) 0 y z + 1 ≤
      clockWindowRemainder n n 6 y z := by
  have hk : n - 1 ≠ n := by omega
  have hlast : n - 1 + 1 = n := by omega
  simp [clockWindowRemainder, hk, hlast] <;> omega

/-- All-n completed-B incoming seam, at the abstract word layer.
    The terminal offset n-1 is the only rewritten follower. -/
theorem clockIncomingCompletedWordMono
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hroot : w 0 = (6 : Fin 8)) :
    startPsiWord n .RUNNING (clockIncomingWord n w) ≤
      startPsiWord n .RUNNING w := by
  let v := clockIncomingWord n w
  let k := firstNonDone w n 0
  have hfirst : firstNonDone w n 0 = k := rfl
  have hkbound : k ≤ n := by
    have hh := (clockFirstNonDoneRange w n 0).2
    simpa only [Nat.zero_add] using hh
  have hzero : v 0 = w 0 := by
    change clockIncomingWord n w 0 = w 0
    exact clockIncomingWordAway n w 0 (by omega)
  have hz : (w 0).val = 6 := by
    rw [hroot]
    rfl
  have hzv : (v 0).val = 6 := by
    rw [hzero]
    exact hz
  have hw :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by omega
  have hv :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by omega
  have hlastVal : v (n - 1) =
      clockIncomingShape (w (n - 1)) :=
    clockIncomingWordAt n w
  have hlastNot : (v (n - 1)).val ≠ 6 := by
    rw [hlastVal]
    exact clockIncomingShapeNotDone (w (n - 1))
  by_cases hlate : n - 1 ≤ k
  · have hpre : ∀ i, i < n - 1 → (v i).val = 6 := by
      intro i hi
      have hp : i < k := by omega
      have hd := clockFirstNonDonePrefixDone w n 0 i
        (by omega) (by
          rw [hfirst]
          exact hp)
      have hfr : v i = w i :=
        clockIncomingWordAway n w i (by omega)
      rw [hfr]
      exact hd
    have hfirstV : firstNonDone v n 0 = n - 1 := by
      have hh := clockFirstNonDoneAt v n 0 (n - 1)
        (by omega)
        (by
          intro i hi
          simpa only [Nat.zero_add] using hpre i hi)
        (by simpa only [Nat.zero_add] using hlastNot)
      simpa only [Nat.zero_add] using hh
    have hafter := clockPsiRunningWindow n (n - 1) v hv hfirstV
    have hbefore := clockPsiRunningWindow n k w hw hfirst
    change startPsiWord n .RUNNING v ≤
      startPsiWord n .RUNNING w
    rw [hafter, hbefore]
    by_cases hdone : k = n
    · have hlastDone : (w (n - 1)).val = 6 := by
        exact clockFirstNonDonePrefixDone w n 0 (n - 1)
          (by omega) (by
            rw [hfirst, hdone]
            omega)
      have hlastSix : w (n - 1) = (6 : Fin 8) := by
        apply Fin.ext
        exact hlastDone
      have hlastC : v (n - 1) = (0 : Fin 8) := by
        rw [hlastVal, hlastSix]
        decide
      rw [hdone, hlastC]
      have hne : n - 1 ≠ n := by omega
      have hsum : n - 1 + 1 = n := by omega
      simp [clockWindowRemainder, hne, hsum] <;> omega
    · have hkLast : k = n - 1 := by omega
      have hnot : (w (n - 1)).val ≠ 6 := by
        have hb : firstNonDone w n 0 < 0 + n := by
          rw [hfirst, hkLast]
          omega
        have hh := clockFirstNonDoneFrontNotDone w n 0 hb
        rw [hfirst, hkLast] at hh
        exact hh
      rw [hkLast]
      rw [show n - 1 + 1 = n from by omega,
        show n - 1 + 2 = n + 1 from by omega]
      rw [clockLastWindow n (v (n - 1)) (v n) (v (n + 1))
          hn hlastNot,
        clockLastWindow n (w (n - 1)) (w n) (w (n + 1))
          hn hnot,
        hlastVal]
      have hh := clockLastRankIncomingWeak (w (n - 1)) hnot
      omega
  · have hk : k < n - 1 := by omega
    have hfirstV : firstNonDone v n 0 = k := by
      apply clockFirstNonDoneStablePrefix w v n k
        (by omega) hfirst
      intro i hi
      exact (clockIncomingWordAway n w i (by omega)).symm
    by_cases hfar : k + 2 < n - 1
    · have hlocal :
          ∀ i, i ≤ k + 2 → w i = v i := by
        intro i hi
        exact (clockIncomingWordAway n w i (by omega)).symm
      change startPsiWord n .RUNNING v ≤
        startPsiWord n .RUNNING w
      exact Nat.le_of_eq
        (clockPsiWordLocality n .RUNNING w v k
          (by omega) hfirst hlocal).symm
    · have hbefore := clockPsiRunningWindow n k w hw hfirst
      have hafter := clockPsiRunningWindow n k v hv hfirstV
      change startPsiWord n .RUNNING v ≤
        startPsiWord n .RUNNING w
      rw [hafter, hbefore]
      by_cases hthird : k + 2 = n - 1
      · have hx : v k = w k :=
          clockIncomingWordAway n w k (by omega)
        have hy : v (k + 1) = w (k + 1) :=
          clockIncomingWordAway n w (k + 1) (by omega)
        have hthirdValue :
            v (k + 2) = clockIncomingShape (w (k + 2)) := by
          rw [hthird]
          exact hlastVal
        rw [hx, hy, hthirdValue]
        exact clockWindowThirdWeak n k
          (w k) (w (k + 1)) (w (k + 2))
          (clockIncomingShape (w (k + 2)))
          (clockIncomingShapeHighWeak (w (k + 2)))
      · have hkNear : k + 1 = n - 1 := by omega
        have hkEq : k = n - 2 := by omega
        have hnon : (w (n - 2)).val ≠ 6 := by
          have hb : firstNonDone w n 0 < 0 + n := by
            rw [hfirst]
            omega
          have hh := clockFirstNonDoneFrontNotDone w n 0 hb
          rw [hfirst, hkEq] at hh
          exact hh
        have hx : v k = w k :=
          clockIncomingWordAway n w k (by omega)
        have hy :
            v (k + 1) =
              clockIncomingShape (w (k + 1)) := by
          rw [hkNear]
          exact hlastVal
        have hzfar : v (k + 2) = w (k + 2) :=
          clockIncomingWordAway n w (k + 2) (by omega)
        rw [hx, hy, hzfar]
        simp only [hkEq,
          show n - 2 + 1 = n - 1 from by omega,
          show n - 2 + 2 = n from by omega]
        rw [clockNearEndWindow n (w (n - 2))
            (clockIncomingShape (w (n - 1))) (w n) hn hnon,
          clockNearEndWindow n (w (n - 2))
            (w (n - 1)) (w n) hn hnon]
        have hh := clockNearEndRankIncomingWeak
          (w (n - 2)) (w (n - 1))
        omega

/-- Complete (b6) ROOT_IN on the RUNNING/completedB stage. -/
theorem clockIncomingRunningCompletedMono
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n) :
    clockAbstractPsi n
      (rootIn (w (n - 1))
        { cert := .RUNNING, stage := .completedB }).2
      (clockWrite w (n - 1)
        (rootIn (w (n - 1))
          { cert := .RUNNING, stage := .completedB }).1) ≤
    clockAbstractPsi n
      { cert := .RUNNING, stage := .completedB } w := by
  have hr :
      (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := .completedB } : RootClass)).2 =
        { cert := .RUNNING, stage := .completedB } :=
    clockRootIncomingNonidleRootFrame _ _ (by decide)
  have hx :
      (rootIn (w (n - 1))
        ({ cert := .RUNNING, stage := .completedB } : RootClass)).1 =
        clockIncomingShape (w (n - 1)) :=
    clockIncomingShapeLiteral (w (n - 1))
  rw [hr, hx]
  let r : RootClass := { cert := .RUNNING, stage := .completedB }
  let u := clockAbstractWord r w
  have hlast : u (n - 1) = w (n - 1) := by
    simp [u, clockAbstractWord, show n - 1 ≠ 0 from by omega]
  have hword :
      clockAbstractWord r
        (clockWrite w (n - 1) (clockIncomingShape (w (n - 1)))) =
      clockIncomingWord n u := by
    rw [clockAbstractWordWrite r w (n - 1)
      (clockIncomingShape (w (n - 1))) (by omega)]
    simp only [clockIncomingWord, hlast]
    change clockWrite u (n - 1)
        (clockIncomingShape (w (n - 1))) =
      clockWrite u (n - 1)
        (clockIncomingShape (w (n - 1)))
    rfl
  have hroot : u 0 = (6 : Fin 8) := by
    change clockRootShape r = (6 : Fin 8)
    rfl
  change startPsiWord n .RUNNING
      (clockAbstractWord r
        (clockWrite w (n - 1)
          (clockIncomingShape (w (n - 1))))) ≤
    startPsiWord n .RUNNING u
  rw [hword]
  exact clockIncomingCompletedWordMono n u hn hroot

/-- (b6) Every ROOT_IN step, for every root class, n>=4 and
    every Cartesian follower word, is nonincreasing. -/
theorem clockRootInMono
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8) :
    clockAbstractPsi n
      (rootIn (w (n - 1)) r).2
      (clockWrite w (n - 1) (rootIn (w (n - 1)) r).1) ≤
    clockAbstractPsi n r w := by
  cases r with
  | mk cert st =>
    cases cert with
    | IDLE =>
      exact clockIncomingIdleDecrease n
        { cert := .IDLE, stage := st } w rfl
    | REQUESTED =>
      rw [clockIncomingRequestedFrame n
        { cert := .REQUESTED, stage := st } w rfl]
      exact Nat.le_refl _
    | RUNNING =>
      cases st with
      | completedB =>
        exact clockIncomingRunningCompletedMono n w hn
      | freshB =>
        exact clockIncomingRunningBeforeCompleted
          n hn .freshB w (by decide)
      | waitingB =>
        exact clockIncomingRunningBeforeCompleted
          n hn .waitingB w (by decide)
      | nonB =>
        exact clockIncomingRunningBeforeCompleted
          n hn .nonB w (by decide)

/-- Every legal INTERNAL update is nonincreasing on the exact
    infinite shape word, with arbitrary root certificate.
    In particular k=n is handled by the B/DONE prefix frame. -/
theorem clockInternalEveryOffsetMono
    (n : Nat) (hn : 4 ≤ n) (cert : SerCert)
    (w : Nat → Fin 8) (p : Nat)
    (hp : 0 < p) (hnext : p + 1 < n) :
    startPsiWord n cert (clockInternalWord w p) ≤
      startPsiWord n cert w := by
  let k := firstNonDone w n 0
  have hfirst : firstNonDone w n 0 = k := rfl
  have hkbound : k ≤ n := by
    have hb := (clockFirstNonDoneRange w n 0).2
    simpa only [Nat.zero_add] using hb
  by_cases hdone : k = n
  · have hinside : p + 1 < k := by omega
    rw [clockInternalInsideWord w n k p hfirst hinside]
    exact Nat.le_refl _
  · have hk : k < n := by omega
    by_cases hinside : p + 1 < k
    · rw [clockInternalInsideWord w n k p hfirst hinside]
      exact Nat.le_refl _
    · by_cases hleft : p + 1 = k
      · have hkp : 2 ≤ k := by omega
        have hpeq : p = k - 1 := by omega
        rw [hpeq]
        exact clockInternalLeftMono w n k cert
          hn hkp hk hfirst
      · by_cases hcenter : p = k
        · rw [hcenter]
          exact clockInternalCentralMono w n k cert hn
            (by omega) (by omega) hfirst
        · by_cases hmiddle : p = k + 1
          · have htwo : k + 2 < n := by omega
            rw [hmiddle]
            exact (clockInternalMiddleLookaheadMono
              w n k cert hn htwo hfirst).2
          · by_cases hthird : p = k + 2
            · have hthree : k + 3 < n := by omega
              rw [hthird]
              rw [(clockInternalThirdLookaheadFrame
                w n k cert hk hfirst hthree).2]
              exact Nat.le_refl _
            · have hfar : k + 2 < p := by omega
              rw [(clockInternalFarFrame
                w n k p cert hk hfirst hfar).2]
              exact Nat.le_refl _

/-- Root encoding at a positive offset is exactly the follower
    shape, irrespective of the root class. -/
theorem clockAbstractPositiveShape
    (r : RootClass) (w : Nat → Fin 8) (p : Nat)
    (hp : 0 < p) :
    clockAbstractWord r w p = w p := by
  simp [clockAbstractWord, show p ≠ 0 from by omega]

/-- The two-site INTERNAL update commutes with insertion of the
    canonical root shape. -/
theorem clockAbstractInternalWord
    (r : RootClass) (w : Nat → Fin 8) (p : Nat)
    (hp : 0 < p) :
    clockAbstractWord r (clockInternalWord w p) =
      clockInternalWord (clockAbstractWord r w) p := by
  have hs : clockAbstractWord r w p = w p :=
    clockAbstractPositiveShape r w p hp
  have ht : clockAbstractWord r w (p + 1) = w (p + 1) :=
    clockAbstractPositiveShape r w (p + 1) (by omega)
  calc
    clockAbstractWord r (clockInternalWord w p) =
        clockWrite
          (clockWrite (clockAbstractWord r w) p
            (followerPair (w p) (w (p + 1))).1)
          (p + 1) (followerPair (w p) (w (p + 1))).2 := by
      simp only [clockInternalWord]
      rw [clockAbstractWordWrite r
          (clockWrite w p
            (followerPair (w p) (w (p + 1))).1)
          (p + 1)
          (followerPair (w p) (w (p + 1))).2 (by omega),
        clockAbstractWordWrite r w p
          (followerPair (w p) (w (p + 1))).1 hp]
    _ = clockInternalWord (clockAbstractWord r w) p := by
      simp only [clockInternalWord, hs, ht]

/-- The INTERNAL third kind at the RootClass + follower-word
    level, for all legal offsets and every n>=4. -/
theorem clockAbstractInternalMono
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8) (p : Nat)
    (hp : 0 < p) (hnext : p + 1 < n) :
    clockAbstractPsi n r (clockInternalWord w p) ≤
      clockAbstractPsi n r w := by
  change startPsiWord n r.cert
      (clockAbstractWord r (clockInternalWord w p)) ≤
    startPsiWord n r.cert (clockAbstractWord r w)
  rw [clockAbstractInternalWord r w p hp]
  exact clockInternalEveryOffsetMono n hn r.cert
    (clockAbstractWord r w) p hp hnext

inductive ClockAbstractEdge (n : Nat) where
  | internal (p : Nat) (hpos : 0 < p) (hnext : p + 1 < n)
  | outgoing
  | incoming

def clockAbstractStep (n : Nat) (r : RootClass)
    (w : Nat → Fin 8) (e : ClockAbstractEdge n) :
    Option (RootClass × (Nat → Fin 8)) :=
  match e with
  | .internal p _ _ => some (r, clockInternalWord w p)
  | .outgoing =>
    match rootOut r (w 1) with
    | none => none
    | some (r', y) => some (r', clockWrite w 1 y)
  | .incoming =>
    some ((rootIn (w (n - 1)) r).2,
      clockWrite w (n - 1) (rootIn (w (n - 1)) r).1)

/-- The terminal case is the REQUESTED root's S1 outgoing
    transition; all other abstract steps return a successor. -/
theorem clockAbstractOutgoingTerminalIff
    (n : Nat) (r : RootClass) (w : Nat → Fin 8) :
    clockAbstractStep n r w .outgoing = none ↔
      r.cert = .REQUESTED := by
  unfold clockAbstractStep
  constructor
  · intro h
    by_cases hc : r.cert = .REQUESTED
    · exact hc
    · have hs : ∃ r' y,
          rootOut r (w 1) = some (r', y) := by
        cases hstage : r.stage with
        | nonB =>
          exact ⟨{ cert := .IDLE, stage := .waitingB }, 1,
            by simp [rootOut, hc, hstage]⟩
        | freshB =>
          exact ⟨{ cert := r.cert, stage := .waitingB }, 1,
            by simp [rootOut, hc, hstage]⟩
        | waitingB =>
          by_cases hy : (w 1).val = 1
          · exact ⟨r, w 1, by simp [rootOut, hc, hstage, hy]⟩
          · by_cases hz : (w 1).val = 2
            · exact ⟨{ cert := r.cert, stage := .completedB }, 4,
                by simp [rootOut, hc, hstage, hy, hz]⟩
            · by_cases ht : (w 1).val = 3
              · exact ⟨{ cert := r.cert, stage := .completedB }, 7,
                  by simp [rootOut, hc, hstage, hy, hz, ht]⟩
              · exact ⟨{ cert := r.cert, stage := .waitingB }, 1,
                  by simp [rootOut, hc, hstage, hy, hz, ht]⟩
        | completedB =>
          by_cases hy : (w 1).val = 7
          · exact ⟨{ cert := .IDLE, stage := .nonB }, w 1,
              by simp [rootOut, hc, hstage, hy]⟩
          · by_cases hz : 4 ≤ (w 1).val
            · exact ⟨r, w 1,
                by simp [rootOut, hc, hstage, hy, hz]⟩
            · exact ⟨{ cert := r.cert, stage := .waitingB }, 1,
                by simp [rootOut, hc, hstage, hy, hz]⟩
      obtain ⟨r', y, hs⟩ := hs
      simp [hs] at h
  · intro hc
    simp [clockAbstractStep, rootOut, hc]

/-- (b7) Every actual nonterminal abstract edge is monotone.
    The terminal S1 outgoing event is represented by none. -/
theorem clockAbstractEveryEdgeMono
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8)
    (e : ClockAbstractEdge n)
    (r' : RootClass) (v : Nat → Fin 8)
    (hstep : clockAbstractStep n r w e = some (r', v)) :
    clockAbstractPsi n r' v ≤ clockAbstractPsi n r w := by
  cases e with
  | internal p hp hnext =>
    change some (r, clockInternalWord w p) = some (r', v)
      at hstep
    have he := Option.some.inj hstep
    have hr : r' = r := (congrArg Prod.fst he).symm
    have hv : v = clockInternalWord w p :=
      (congrArg Prod.snd he).symm
    rw [hr, hv]
    exact clockAbstractInternalMono n hn r w p hp hnext
  | outgoing =>
    change (match rootOut r (w 1) with
      | none => none
      | some (r0, y0) => some (r0, clockWrite w 1 y0)) =
        some (r', v) at hstep
    cases hrow : rootOut r (w 1) with
    | none =>
      simp [hrow] at hstep
    | some pair =>
      cases pair with
      | mk rOut y =>
        have he : some (rOut, clockWrite w 1 y) =
            some (r', v) := by
          simpa only [hrow] using hstep
        have hpair := Option.some.inj he
        have hr : r' = rOut :=
          (congrArg Prod.fst hpair).symm
        have hv : v = clockWrite w 1 y :=
          (congrArg Prod.snd hpair).symm
        rw [hr, hv]
        have hc : r.cert ≠ .REQUESTED := by
          intro hh
          have hnone := rootOut_none_of_requested r (w 1) hh
          rw [hnone] at hrow
          cases hrow
        exact clockRootOutNonSOneMono n hn r w rOut y hc hrow
  | incoming =>
    change some ((rootIn (w (n - 1)) r).2,
      clockWrite w (n - 1) (rootIn (w (n - 1)) r).1) =
        some (r', v) at hstep
    have hpair := Option.some.inj hstep
    have hr : r' = (rootIn (w (n - 1)) r).2 :=
      (congrArg Prod.fst hpair).symm
    have hv : v =
        clockWrite w (n - 1) (rootIn (w (n - 1)) r).1 :=
      (congrArg Prod.snd hpair).symm
    rw [hr, hv]
    exact clockRootInMono n hn r w

end L3

namespace L3

set_option autoImplicit false

/-!
Nominated strict-decrease edges.
This section first
restates the known strict edges for the other root classes, then
adds completedB witnesses for C/F and B/NEW frontiers.
-/

def clockStrictEdge
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (e : ClockAbstractEdge n) : Prop :=
  match clockAbstractStep n r w e with
  | none => 1 ≤ clockAbstractPsi n r w
  | some (r', v) =>
    clockAbstractPsi n r' v + 1 ≤ clockAbstractPsi n r w

theorem clockRequestedNominated
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hc : r.cert = .REQUESTED) :
    clockStrictEdge n r w .outgoing := by
  have ht := (clockAbstractOutgoingTerminalIff n r w).2 hc
  simp [clockStrictEdge, ht, clockAbstractPsi,
    startPsiWord, hc]

theorem clockIdleNominated
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hc : r.cert = .IDLE) :
    clockStrictEdge n r w .incoming := by
  have hafter :
      (rootIn (w (n - 1)) r).2.cert = .REQUESTED := by
    simp [rootIn, hc]
  unfold clockStrictEdge clockAbstractStep
  simp [clockAbstractPsi, startPsiWord, hc, hafter]

theorem clockNonBNominated
    (n : Nat) (w : Nat → Fin 8) :
    clockStrictEdge n
      { cert := .RUNNING, stage := .nonB } w .outgoing := by
  have hstrict := clockRootOutNonBStrict n w
    ({ cert := .IDLE, stage := .waitingB } : RootClass)
    1 rfl
  simpa [clockStrictEdge, clockAbstractStep, rootOut]
    using hstrict

theorem clockFreshNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n) :
    clockStrictEdge n
      { cert := .RUNNING, stage := .freshB } w .outgoing := by
  have hstrict := clockRootFreshChallengeStrict n w hn
  simpa [clockStrictEdge, clockAbstractStep, rootOut]
    using hstrict

/-- An INTERNAL edge serving a PENDING child at offset one
    strictly decreases the finite middle-window rank, irrespective
    of its responder shape. -/
theorem clockPendingMiddleRankStrict :
    ∀ z : Fin 8,
      clockMiddleRank
          (followerPair (1 : Fin 8) z).1
          (followerPair (1 : Fin 8) z).2 + 1 ≤
        clockMiddleRank (1 : Fin 8) z := by
  decide

theorem clockPendingMiddleNonleaf :
    ∀ z : Fin 8,
      (followerPair (1 : Fin 8) z).1.val ≠ 3 := by
  decide

/-- RUNNING B/WAIT, PENDING at child one: choose INTERNAL edge
    p=1. The challenge/observation strictly reduces Psi. -/
theorem clockRootWaitPendingInternalStrict
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hp : w 1 = (1 : Fin 8)) :
    clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB }
        (clockInternalWord w 1) + 1 ≤
      clockAbstractPsi n
        { cert := .RUNNING, stage := .waitingB } w := by
  rw [clockRootWaitRemainder n (clockInternalWord w 1)
      (by omega),
    clockRootWaitRemainder n w (by omega)]
  rw [clockInternalWordSource, clockInternalWordTarget, hp]
  have hnew := clockWindowMiddleBulk n 0
    (followerPair (1 : Fin 8) (w 2)).1
    (followerPair (1 : Fin 8) (w 2)).2
    hn (by omega)
  have hold := clockWindowMiddleBulk n 0 (1 : Fin 8)
    (w 2) hn (by omega)
  rw [hnew, hold]
  have hpnot := clockPendingMiddleNonleaf (w 2)
  have holdnot : ((1 : Fin 8).val ≠ 3) := by decide
  rw [if_neg hpnot, if_neg holdnot]
  have hrank := clockPendingMiddleRankStrict (w 2)
  omega

theorem clockRootWaitPendingNominated
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hp : w 1 = (1 : Fin 8)) :
    clockStrictEdge n
      { cert := .RUNNING, stage := .waitingB } w
      (.internal 1 (by omega) (by omega)) := by
  have hh := clockRootWaitPendingInternalStrict n w hn hp
  simpa only [clockStrictEdge, clockAbstractStep] using hh

theorem clockRootWaitNonpendingNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hp : w 1 ≠ (1 : Fin 8)) :
    clockStrictEdge n
      { cert := .RUNNING, stage := .waitingB } w .outgoing := by
  by_cases hi : w 1 = (2 : Fin 8)
  · have hh := clockRootWaitInternalStrict n w hn hi
    simpa [clockStrictEdge, clockAbstractStep, rootOut, hi]
      using hh
  · by_cases hl : w 1 = (3 : Fin 8)
    · have hh := clockRootWaitLeafStrict n w hn hl
      simpa [clockStrictEdge, clockAbstractStep, rootOut, hl]
        using hh
    · have hpv : (w 1).val ≠ 1 := by
        intro hv
        apply hp
        apply Fin.ext
        simpa only [clockFinValOne] using hv
      have hiv : (w 1).val ≠ 2 := by
        intro hv
        apply hi
        apply Fin.ext
        simpa only [clockFinValTwo] using hv
      have hlv : (w 1).val ≠ 3 := by
        intro hv
        apply hl
        apply Fin.ext
        simpa only [clockFinValThree] using hv
      have hh := clockRootWaitOtherStrict n w hn hpv hiv hlv
      simpa [clockStrictEdge, clockAbstractStep, rootOut,
        hpv, hiv, hlv] using hh

/-- The RUNNING B/WAIT root has a nominated strict edge at every
    Cartesian follower word. The edge may be root-out or p=1. -/
theorem clockRootWaitNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n) :
    ∃ e : ClockAbstractEdge n,
      clockStrictEdge n
        { cert := .RUNNING, stage := .waitingB } w e := by
  by_cases hp : w 1 = (1 : Fin 8)
  · refine ⟨.internal 1 (by omega) (by omega), ?_⟩
    exact clockRootWaitPendingNominated n w hn hp
  · exact ⟨.outgoing,
      clockRootWaitNonpendingNominated n w hn hp⟩

/-- The RUNNING completed-B root, in canonical abstract form. -/
def clockCompletedRoot : RootClass :=
  { cert := .RUNNING, stage := .completedB }

/-- Transfer strict potential drop on a root-relative shape word
    to a genuine non-root INTERNAL abstract edge. -/
theorem clockInternalStrictOfWord
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (p : Nat) (hp : 0 < p) (hnext : p + 1 < n)
    (hstrict :
      startPsiWord n r.cert
        (clockInternalWord (clockAbstractWord r w) p) + 1 ≤
      startPsiWord n r.cert (clockAbstractWord r w)) :
    clockStrictEdge n r w (.internal p hp hnext) := by
  change clockAbstractPsi n r (clockInternalWord w p) + 1 ≤
    clockAbstractPsi n r w
  change startPsiWord n r.cert
    (clockAbstractWord r (clockInternalWord w p)) + 1 ≤
    startPsiWord n r.cert (clockAbstractWord r w)
  rw [clockAbstractInternalWord r w p hp]
  exact hstrict

/-- A completed-B root whose first unfinished follower at k>=2
    is a C shape has a strict predecessor edge k-1. -/
theorem clockCompletedLeftCNominated
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hk : 2 ≤ k) (hkn : k < n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = k)
    (hc : (w k).val ≤ 3) :
    clockStrictEdge n clockCompletedRoot w
      (.internal (k - 1) (by omega) (by omega)) := by
  apply clockInternalStrictOfWord n clockCompletedRoot w (k - 1)
    (by omega) (by omega)
  have hshape : ((clockAbstractWord clockCompletedRoot w) k).val ≤ 3 := by
    rw [clockAbstractPositiveShape clockCompletedRoot w k (by omega)]
    exact hc
  change startPsiWord n .RUNNING
      (clockInternalWord (clockAbstractWord clockCompletedRoot w) (k - 1)) +
      1 ≤ startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  exact clockInternalLeftCWordStrict
    (clockAbstractWord clockCompletedRoot w) n k hn hk hkn hfirst hshape

/-- A returning F at k>=2 has the same strict predecessor nomination. -/
theorem clockCompletedLeftFNominated
    (n k : Nat) (w : Nat → Fin 8)
    (hk : 2 ≤ k) (hkn : k < n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = k)
    (hf : w k = (7 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w
      (.internal (k - 1) (by omega) (by omega)) := by
  apply clockInternalStrictOfWord n clockCompletedRoot w (k - 1)
    (by omega) (by omega)
  have hshape :
      clockAbstractWord clockCompletedRoot w k = (7 : Fin 8) := by
    rw [clockAbstractPositiveShape clockCompletedRoot w k (by omega)]
    exact hf
  change startPsiWord n .RUNNING
      (clockInternalWord (clockAbstractWord clockCompletedRoot w) (k - 1)) +
      1 ≤ startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  exact clockInternalLeftFWordStrict
    (clockAbstractWord clockCompletedRoot w) n k hk hkn hfirst hshape

/-- A B/NEW frontier has a nominated outgoing INTERNAL edge k
    whenever k<n-1. -/
theorem clockCompletedFreshFrontierNominated
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hk : 0 < k) (hnext : k + 1 < n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = k)
    (hx : w k = (4 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w
      (.internal k hk hnext) := by
  apply clockInternalStrictOfWord n clockCompletedRoot w k hk hnext
  have hshape :
      clockAbstractWord clockCompletedRoot w k = (4 : Fin 8) := by
    rw [clockAbstractPositiveShape clockCompletedRoot w k hk]
    exact hx
  change startPsiWord n .RUNNING
      (clockInternalWord (clockAbstractWord clockCompletedRoot w) k) +
      1 ≤ startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  exact clockInternalFrontierFreshStrict n k
    (clockAbstractWord clockCompletedRoot w)
    hn hk hnext hfirst hshape

/-- A C frontier immediately beside the root is serviced by
    the ROOT_OUT S2R challenge rather than an INTERNAL edge. -/
theorem clockCompletedFirstCNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hc : (w 1).val ≤ 3) :
    clockStrictEdge n clockCompletedRoot w .outgoing := by
  have hf : (w 1).val ≠ 7 := by omega
  have hb : ¬ 4 ≤ (w 1).val := by omega
  have hh := clockRootCompletedCStrict n w hn hc
  simpa [clockStrictEdge, clockAbstractStep,
    clockCompletedRoot, rootOut, hf, hb] using hh

end L3

namespace L3

set_option autoImplicit false

/-! Repaired continuation. -/

/-- F immediately beside a completed root selects the terminal
    S6 row, which lowers the certificate from RUNNING to IDLE. -/
theorem clockCompletedFirstFNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hf : w 1 = (7 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w .outgoing := by
  have hh := clockRootCompletedFinishStrict n w hn hf
  have hrow :
      rootOut clockCompletedRoot (w 1) =
        some ({ cert := .IDLE, stage := .nonB }, w 1) := by
    simp [clockCompletedRoot, rootOut, hf]
  unfold clockStrictEdge clockAbstractStep
  rw [hrow]
  change clockAbstractPsi n
      { cert := .IDLE, stage := .nonB }
      (clockWrite w 1 (w 1)) + 1 ≤
    clockAbstractPsi n clockCompletedRoot w
  rw [clockWriteSelf]
  exact hh

end L3


namespace L3

set_option autoImplicit false

/-! completed-B WAIT/PENDING strict middle row.
-/

/-- A B/WAIT frontier whose right child is PENDING improves
    strictly when the child serves the following follower. -/
theorem clockInternalMiddlePendingStrict
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hk : 0 < k) (hnext : k + 2 < n)
    (hfirst : firstNonDone w n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hy : w (k + 1) = (1 : Fin 8)) :
    startPsiWord n .RUNNING (clockInternalWord w (k + 1)) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockInternalWord w (k + 1)
  have hfront : firstNonDone v n 0 = k :=
    (clockInternalMiddleLookaheadMono
      w n k .RUNNING hn hnext hfirst).1
  have hroot : (w 0).val = 6 :=
    clockFirstNonDonePrefixDone w n 0 0 (by omega) (by
      rw [hfirst]
      omega)
  have hzero : v 0 = w 0 :=
    clockInternalWordRemote w (k + 1) 0 (by omega) (by omega)
  have hrootV : (v 0).val = 6 := by
    rw [hzero]
    exact hroot
  have hnotW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by omega
  have hnotV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by omega
  have hsource : v k = w k :=
    clockInternalWordRemote w (k + 1) k (by omega) (by omega)
  have hmiddle : v (k + 1) =
      (followerPair (w (k + 1)) (w (k + 2))).1 :=
    clockInternalWordSource w (k + 1)
  have hright : v (k + 2) =
      (followerPair (w (k + 1)) (w (k + 2))).2 :=
    clockInternalWordTarget w (k + 1)
  have hbefore := clockPsiRunningWindow n k w hnotW hfirst
  have hafter := clockPsiRunningWindow n k v hnotV hfront
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore, hsource, hmiddle, hright, hx, hy]
  rw [clockWindowMiddleBulk n k
      (followerPair (1 : Fin 8) (w (k + 2))).1
      (followerPair (1 : Fin 8) (w (k + 2))).2
      hn hnext,
    clockWindowMiddleBulk n k (1 : Fin 8) (w (k + 2))
      hn hnext]
  have hp := clockPendingMiddleNonleaf (w (k + 2))
  have hq : ((1 : Fin 8).val ≠ 3) := by decide
  rw [if_neg hp, if_neg hq]
  have hstrict := clockPendingMiddleRankStrict (w (k + 2))
  omega

/-- Complete-B/PENDING nomination for k+2<n. -/
theorem clockCompletedPendingMiddleNominated
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hk : 0 < k) (hnext : k + 2 < n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hy : w (k + 1) = (1 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w
      (.internal (k + 1) (by omega) hnext) := by
  apply clockInternalStrictOfWord n clockCompletedRoot w (k + 1)
    (by omega) hnext
  have hshape :
      clockAbstractWord clockCompletedRoot w k = (5 : Fin 8) := by
    rw [clockAbstractPositiveShape clockCompletedRoot w k hk]
    exact hx
  have hchild :
      clockAbstractWord clockCompletedRoot w (k + 1) = (1 : Fin 8) := by
    rw [clockAbstractPositiveShape clockCompletedRoot w (k + 1)
      (by omega)]
    exact hy
  change startPsiWord n .RUNNING
      (clockInternalWord (clockAbstractWord clockCompletedRoot w) (k + 1)) +
      1 ≤ startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  exact clockInternalMiddlePendingStrict n k
    (clockAbstractWord clockCompletedRoot w)
    hn hk hnext hfirst hshape hchild

end L3


namespace L3

set_option autoImplicit false

/-! B/WAIT non-PENDING completed-root nomination.
-/

theorem clockCompletedWaitNonpendingNominated
    (n k : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hk : 0 < k) (hnext : k + 1 < n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = k)
    (hx : w k = (5 : Fin 8))
    (hnotPending : w (k + 1) ≠ (1 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w
      (.internal k hk hnext) := by
  apply clockInternalStrictOfWord n clockCompletedRoot w k hk hnext
  have hshape :
      clockAbstractWord clockCompletedRoot w k = (5 : Fin 8) := by
    rw [clockAbstractPositiveShape clockCompletedRoot w k hk]
    exact hx
  have hchild :
      clockAbstractWord clockCompletedRoot w (k + 1) = w (k + 1) :=
    clockAbstractPositiveShape clockCompletedRoot w (k + 1) (by omega)
  change startPsiWord n .RUNNING
      (clockInternalWord (clockAbstractWord clockCompletedRoot w) k) +
      1 ≤ startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  by_cases hi : w (k + 1) = (2 : Fin 8)
  · have hy :
        clockAbstractWord clockCompletedRoot w (k + 1) =
          (2 : Fin 8) := by
      rw [hchild]
      exact hi
    exact clockInternalWaitInternalWordStrict
      (clockAbstractWord clockCompletedRoot w)
      n k hn hk hnext hfirst hshape hy
  · by_cases hl : w (k + 1) = (3 : Fin 8)
    · have hy :
          clockAbstractWord clockCompletedRoot w (k + 1) =
            (3 : Fin 8) := by
        rw [hchild]
        exact hl
      exact clockInternalWaitLeafWordStrict
        (clockAbstractWord clockCompletedRoot w)
        n k hn hk hnext hfirst hshape hy
    · have hp : (w (k + 1)).val ≠ 1 := by
        intro hh
        apply hnotPending
        apply Fin.ext
        simpa only [clockFinValOne] using hh
      have hiV : (w (k + 1)).val ≠ 2 := by
        intro hh
        apply hi
        apply Fin.ext
        simpa only [clockFinValTwo] using hh
      have hlV : (w (k + 1)).val ≠ 3 := by
        intro hh
        apply hl
        apply Fin.ext
        simpa only [clockFinValThree] using hh
      have hp' :
          (clockAbstractWord clockCompletedRoot w (k + 1)).val ≠ 1 := by
        rw [hchild]
        exact hp
      have hi' :
          (clockAbstractWord clockCompletedRoot w (k + 1)).val ≠ 2 := by
        rw [hchild]
        exact hiV
      have hl' :
          (clockAbstractWord clockCompletedRoot w (k + 1)).val ≠ 3 := by
        rw [hchild]
        exact hlV
      exact clockInternalCentralWaitOtherStrict
        (clockAbstractWord clockCompletedRoot w)
        n k hn hk hnext hfirst hshape hp' hi' hl'

end L3


namespace L3

set_option autoImplicit false

/-! Terminal ROOT_IN strict edge certificates.
-/

/-- All-DONE completed-root word: ROOT_IN converts the final DONE
    to C/NONE and decreases Psi by one. -/
theorem clockIncomingAllDoneWordStrict
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hroot : w 0 = (6 : Fin 8))
    (hfirst : firstNonDone w n 0 = n) :
    startPsiWord n .RUNNING (clockIncomingWord n w) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockIncomingWord n w
  have hlast : w (n - 1) = (6 : Fin 8) := by
    apply Fin.ext
    exact clockFirstNonDonePrefixDone w n 0 (n - 1)
      (by omega) (by
        rw [hfirst]
        omega)
  have hlastV : v (n - 1) = (0 : Fin 8) := by
    change clockIncomingWord n w (n - 1) = (0 : Fin 8)
    rw [clockIncomingWordAt, hlast]
    decide
  have hfirstV : firstNonDone v n 0 = n - 1 :=
    clockIncomingFirstLate w n n hn (by omega) hfirst (by
      change (v (n - 1)).val ≠ 6
      rw [hlastV]
      decide)
  have hzero : v 0 = w 0 :=
    clockIncomingWordAway n w 0 (by omega)
  have hnotW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by
    rw [hroot]
    decide
  have hnotV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
    rw [hzero]
    exact hnotW
  have hbefore := clockPsiRunningWindow n n w hnotW hfirst
  have hafter := clockPsiRunningWindow n (n - 1) v hnotV hfirstV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore, hlastV]
  have hk : n - 1 ≠ n := by omega
  have he : n - 1 + 1 = n := by omega
  simp [clockWindowRemainder, hk, he] <;> omega

/-- Final frontier B/NEW or B/WAIT: converting it to C/NONE
    strictly lowers the last-offset potential n+5 to n+4. -/
theorem clockIncomingLastBandWordStrict
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hroot : w 0 = (6 : Fin 8))
    (hfirst : firstNonDone w n 0 = n - 1)
    (hband : 4 ≤ (w (n - 1)).val ∧ (w (n - 1)).val ≤ 5) :
    startPsiWord n .RUNNING (clockIncomingWord n w) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockIncomingWord n w
  have hnOne : (w (n - 1)).val ≠ 1 := by omega
  have hbandSix :
      4 ≤ (w (n - 1)).val ∧ (w (n - 1)).val ≤ 6 := by
    omega
  have hlastV : v (n - 1) = (0 : Fin 8) := by
    change clockIncomingWord n w (n - 1) = (0 : Fin 8)
    rw [clockIncomingWordAt]
    simp [clockIncomingShape, hnOne, hbandSix]
  have hfirstV : firstNonDone v n 0 = n - 1 :=
    clockIncomingFirstLate w n (n - 1) hn
      (by omega) hfirst (by
        change (v (n - 1)).val ≠ 6
        rw [hlastV]
        decide)
  have hzero : v 0 = w 0 :=
    clockIncomingWordAway n w 0 (by omega)
  have hnotW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by
    rw [hroot]
    decide
  have hnotV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
    rw [hzero]
    exact hnotW
  have holdNot : (w (n - 1)).val ≠ 6 := by omega
  have hnewNot : (v (n - 1)).val ≠ 6 := by
    rw [hlastV]
    decide
  have hbefore := clockPsiRunningWindow n (n - 1) w hnotW hfirst
  have hafter := clockPsiRunningWindow n (n - 1) v hnotV hfirstV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore]
  rw [show n - 1 + 1 = n from by omega,
      show n - 1 + 2 = n + 1 from by omega]
  rw [clockLastWindow n (v (n - 1)) (v n) (v (n + 1))
        hn hnewNot,
      clockLastWindow n (w (n - 1)) (w n) (w (n + 1))
        hn holdNot,
      hlastV]
  have hrNew : clockLastRank (0 : Fin 8) = 4 := by decide
  have hrOld : clockLastRank (w (n - 1)) = 5 := by
    have hnotSeven : (w (n - 1)).val ≠ 7 := by omega
    have hnotC : ¬ (w (n - 1)).val ≤ 3 := by omega
    have hFourFive :
        (w (n - 1)).val = 4 ∨ (w (n - 1)).val = 5 := by omega
    simp [clockLastRank, hnotSeven, hnotC, hFourFive]
  rw [hrNew, hrOld]
  omega

/-- A WAIT/PENDING frontier at n-2 chooses ROOT_IN to
    convert its last child from PENDING to LEAF_OK. -/
theorem clockIncomingNearPendingWordStrict
    (n : Nat) (w : Nat → Fin 8)
    (hn : 4 ≤ n) (hroot : w 0 = (6 : Fin 8))
    (hfirst : firstNonDone w n 0 = n - 2)
    (hx : w (n - 2) = (5 : Fin 8))
    (hy : w (n - 1) = (1 : Fin 8)) :
    startPsiWord n .RUNNING (clockIncomingWord n w) + 1 ≤
      startPsiWord n .RUNNING w := by
  let v := clockIncomingWord n w
  have hfirstV : firstNonDone v n 0 = n - 2 :=
    clockIncomingFirstEarly w n (n - 2) hn (by omega) hfirst
  have hzero : v 0 = w 0 :=
    clockIncomingWordAway n w 0 (by omega)
  have hnotW :
      ¬ ((w 0).val ≤ 3 ∨ (w 0).val = 7) := by
    rw [hroot]
    decide
  have hnotV :
      ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
    rw [hzero]
    exact hnotW
  have hleft : v (n - 2) = w (n - 2) :=
    clockIncomingWordAway n w (n - 2) (by omega)
  have hlast : v (n - 1) = (3 : Fin 8) := by
    change clockIncomingWord n w (n - 1) = (3 : Fin 8)
    rw [clockIncomingWordAt, hy]
    decide
  have hright : v n = w n :=
    clockIncomingWordAway n w n (by omega)
  have hbefore := clockPsiRunningWindow n (n - 2) w hnotW hfirst
  have hafter := clockPsiRunningWindow n (n - 2) v hnotV hfirstV
  change startPsiWord n .RUNNING v + 1 ≤
    startPsiWord n .RUNNING w
  rw [hafter, hbefore]
  rw [show n - 2 + 1 = n - 1 from by omega,
      show n - 2 + 2 = n from by omega]
  rw [hleft, hlast, hright, hx, hy]
  rw [clockNearEndWindow n 5 3 (w n) hn (by decide),
      clockNearEndWindow n 5 1 (w n) hn (by decide)]
  have hnew : clockNearEndRank 5 3 = 2 := by decide
  have hold : clockNearEndRank 5 1 = 3 := by decide
  rw [hnew, hold]
  omega

/-- Any strict completed-root seam comparison on the canonical
    shape word transfers to a strict abstract ROOT_IN edge. -/
theorem clockCompletedIncomingStrictOfWord
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hstrict :
      startPsiWord n .RUNNING
        (clockIncomingWord n
          (clockAbstractWord clockCompletedRoot w)) + 1 ≤
      startPsiWord n .RUNNING
        (clockAbstractWord clockCompletedRoot w)) :
    clockStrictEdge n clockCompletedRoot w .incoming := by
  have hr :
      (rootIn (w (n - 1)) clockCompletedRoot).2 =
        clockCompletedRoot :=
    clockRootIncomingNonidleRootFrame _ _ (by decide)
  have hx :
      (rootIn (w (n - 1)) clockCompletedRoot).1 =
        clockIncomingShape (w (n - 1)) :=
    clockIncomingShapeLiteral (w (n - 1))
  change clockAbstractPsi n
      (rootIn (w (n - 1)) clockCompletedRoot).2
      (clockWrite w (n - 1)
        (rootIn (w (n - 1)) clockCompletedRoot).1) + 1 ≤
    clockAbstractPsi n clockCompletedRoot w
  rw [hr, hx]
  change startPsiWord n .RUNNING
      (clockAbstractWord clockCompletedRoot
        (clockWrite w (n - 1)
          (clockIncomingShape (w (n - 1))))) + 1 ≤
    startPsiWord n .RUNNING (clockAbstractWord clockCompletedRoot w)
  have hpos : 0 < n - 1 := by omega
  rw [clockAbstractWordWrite clockCompletedRoot w (n - 1)
      (clockIncomingShape (w (n - 1))) hpos]
  have hlast :
      clockAbstractWord clockCompletedRoot w (n - 1) =
        w (n - 1) :=
    clockAbstractPositiveShape clockCompletedRoot w (n - 1)
      hpos
  simpa only [clockIncomingWord, hlast] using hstrict

end L3


namespace L3

set_option autoImplicit false

/-! all-n completedB nomination assembly.
-/

theorem clockCompletedRootZero (w : Nat → Fin 8) :
    clockAbstractWord clockCompletedRoot w 0 = (6 : Fin 8) := by
  rfl

/-- The all-DONE word nominates the incoming seam. -/
theorem clockCompletedAllDoneNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 = n) :
    clockStrictEdge n clockCompletedRoot w .incoming := by
  let u := clockAbstractWord clockCompletedRoot w
  have hzero : u 0 = (6 : Fin 8) :=
    clockCompletedRootZero w
  have hh := clockIncomingAllDoneWordStrict n u hn hzero hfirst
  exact clockCompletedIncomingStrictOfWord n w hn hh

/-- At the last follower a B/NEW or B/WAIT frontier nominates
    ROOT_IN, which converts it to C/NONE and loses one ticket. -/
theorem clockCompletedLastBandNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 =
        n - 1)
    (hband : 4 ≤ (w (n - 1)).val ∧ (w (n - 1)).val ≤ 5) :
    clockStrictEdge n clockCompletedRoot w .incoming := by
  let u := clockAbstractWord clockCompletedRoot w
  have hzero : u 0 = (6 : Fin 8) :=
    clockCompletedRootZero w
  have hx : u (n - 1) = w (n - 1) :=
    clockAbstractPositiveShape clockCompletedRoot w
      (n - 1) (by omega)
  have hb : 4 ≤ (u (n - 1)).val ∧
      (u (n - 1)).val ≤ 5 := by
    rw [hx]
    exact hband
  have hh := clockIncomingLastBandWordStrict
    n u hn hzero hfirst hb
  exact clockCompletedIncomingStrictOfWord n w hn hh

/-- PENDING at the last follower, immediately to the right
    of a B/WAIT frontier, nominates ROOT_IN. -/
theorem clockCompletedNearPendingNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n)
    (hfirst :
      firstNonDone (clockAbstractWord clockCompletedRoot w) n 0 =
        n - 2)
    (hx : w (n - 2) = (5 : Fin 8))
    (hy : w (n - 1) = (1 : Fin 8)) :
    clockStrictEdge n clockCompletedRoot w .incoming := by
  let u := clockAbstractWord clockCompletedRoot w
  have hzero : u 0 = (6 : Fin 8) :=
    clockCompletedRootZero w
  have hleft : u (n - 2) = (5 : Fin 8) := by
    change clockAbstractWord clockCompletedRoot w (n - 2) =
      (5 : Fin 8)
    rw [clockAbstractPositiveShape clockCompletedRoot w
      (n - 2) (by omega)]
    exact hx
  have hright : u (n - 1) = (1 : Fin 8) := by
    change clockAbstractWord clockCompletedRoot w (n - 1) =
      (1 : Fin 8)
    rw [clockAbstractPositiveShape clockCompletedRoot w
      (n - 1) (by omega)]
    exact hy
  have hh := clockIncomingNearPendingWordStrict
    n u hn hzero hfirst hleft hright
  exact clockCompletedIncomingStrictOfWord n w hn hh

/-- Every RUNNING/completedB abstract word possesses
    a strict edge. The chosen edge is the first non-DONE frontier,
    its predecessor, its PENDING child, or the incoming seam. -/
theorem clockCompletedNominated
    (n : Nat) (w : Nat → Fin 8) (hn : 4 ≤ n) :
    ∃ e : ClockAbstractEdge n,
      clockStrictEdge n clockCompletedRoot w e := by
  let u := clockAbstractWord clockCompletedRoot w
  let k := firstNonDone u n 0
  have hfirst : firstNonDone u n 0 = k := rfl
  have hzero : u 0 = (6 : Fin 8) :=
    clockCompletedRootZero w
  have hkbound : k ≤ n := by
    have hh := (clockFirstNonDoneRange u n 0).2
    simpa only [Nat.zero_add] using hh
  have hkpos : 0 < k := by
    by_cases hkz : k = 0
    · have hlt : firstNonDone u n 0 < 0 + n := by
        rw [hfirst, hkz]
        omega
      have hh := clockFirstNonDoneFrontNotDone u n 0 hlt
      rw [hfirst, hkz, hzero] at hh
      exact False.elim (hh rfl)
    · omega
  by_cases hdone : k = n
  · have hd : firstNonDone u n 0 = n :=
      hfirst.trans hdone
    exact ⟨.incoming, clockCompletedAllDoneNominated n w hn hd⟩
  · have hkn : k < n := by omega
    have hshape : u k = w k :=
      clockAbstractPositiveShape clockCompletedRoot w k hkpos
    have hnotdone : (w k).val ≠ 6 := by
      have hlt : firstNonDone u n 0 < 0 + n := by
        rw [hfirst]
        omega
      have hh := clockFirstNonDoneFrontNotDone u n 0 hlt
      rw [hfirst, hshape] at hh
      exact hh
    by_cases hc : (w k).val ≤ 3
    · by_cases hone : k = 1
      · have hchild : (w 1).val ≤ 3 := by
          rw [← hone]
          exact hc
        exact ⟨.outgoing, clockCompletedFirstCNominated n w hn hchild⟩
      · have htwo : 2 ≤ k := by omega
        exact ⟨.internal (k - 1) (by omega) (by omega),
          clockCompletedLeftCNominated n k w hn htwo hkn
            hfirst hc⟩
    · by_cases hf : (w k).val = 7
      · have hF : w k = (7 : Fin 8) := by
          apply Fin.ext
          simpa only [clockFinValSeven] using hf
        by_cases hone : k = 1
        · have hchild : w 1 = (7 : Fin 8) := by
            rw [← hone]
            exact hF
          exact ⟨.outgoing, clockCompletedFirstFNominated n w hn
            hchild⟩
        · have htwo : 2 ≤ k := by omega
          exact ⟨.internal (k - 1) (by omega) (by omega),
            clockCompletedLeftFNominated n k w htwo hkn
              hfirst hF⟩
      · have hband : (w k).val = 4 ∨ (w k).val = 5 := by
          have hlt := (w k).isLt
          omega
        by_cases hnext : k + 1 < n
        · by_cases hnew : (w k).val = 4
          · have hx : w k = (4 : Fin 8) := by
              apply Fin.ext
              simpa only [clockFinValFour] using hnew
            exact ⟨.internal k hkpos hnext,
              clockCompletedFreshFrontierNominated
                n k w hn hkpos hnext hfirst hx⟩
          · have hwaitVal : (w k).val = 5 := by omega
            have hx : w k = (5 : Fin 8) := by
              apply Fin.ext
              simpa only [clockFinValFive] using hwaitVal
            by_cases hp : w (k + 1) = (1 : Fin 8)
            · by_cases hafter : k + 2 < n
              · exact ⟨.internal (k + 1) (by omega) hafter,
                  clockCompletedPendingMiddleNominated
                    n k w hn hkpos hafter hfirst hx hp⟩
              · have hkNear : k = n - 2 := by omega
                have hfirstNear : firstNonDone u n 0 = n - 2 :=
                  hfirst.trans hkNear
                have hxNear : w (n - 2) = (5 : Fin 8) := by
                  rw [← hkNear]
                  exact hx
                have hyNear : w (n - 1) = (1 : Fin 8) := by
                  have heq : k + 1 = n - 1 := by omega
                  rw [← heq]
                  exact hp
                exact ⟨.incoming,
                  clockCompletedNearPendingNominated
                    n w hn hfirstNear hxNear hyNear⟩
            · exact ⟨.internal k hkpos hnext,
                clockCompletedWaitNonpendingNominated
                  n k w hn hkpos hnext hfirst hx hp⟩
        · have hkLast : k = n - 1 := by omega
          have hfirstLast : firstNonDone u n 0 = n - 1 :=
            hfirst.trans hkLast
          have hlast : 4 ≤ (w (n - 1)).val ∧
              (w (n - 1)).val ≤ 5 := by
            rw [← hkLast]
            omega
          exact ⟨.incoming,
            clockCompletedLastBandNominated n w hn hfirstLast hlast⟩

end L3


namespace L3

set_option autoImplicit false

/-! Combined strict nomination.
-/

/-- Every abstract root-class word has a strict nominated edge,
    counting S1 as an edge to the terminal zero potential. -/
theorem clockAbstractNominated
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (hn : 4 ≤ n) :
    ∃ e : ClockAbstractEdge n, clockStrictEdge n r w e := by
  cases r with
  | mk cert stage =>
    cases cert with
    | REQUESTED =>
      exact ⟨.outgoing,
        clockRequestedNominated n
          { cert := .REQUESTED, stage := stage } w rfl⟩
    | IDLE =>
      exact ⟨.incoming,
        clockIdleNominated n
          { cert := .IDLE, stage := stage } w rfl⟩
    | RUNNING =>
      cases stage with
      | nonB =>
        exact ⟨.outgoing, clockNonBNominated n w⟩
      | freshB =>
        exact ⟨.outgoing, clockFreshNominated n w hn⟩
      | waitingB =>
        exact clockRootWaitNominated n w hn
      | completedB =>
        simpa only [clockCompletedRoot] using
          (clockCompletedNominated n w hn)

/-- Potential of the nonterminal abstract successor; S1 has rank 0. -/
def clockAbstractChildPsi
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (e : ClockAbstractEdge n) : Nat :=
  match clockAbstractStep n r w e with
  | none => 0
  | some (r', v) => clockAbstractPsi n r' v

/-- Every abstract child has a potential no greater than the parent. -/
theorem clockAbstractChildWeak
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8)
    (e : ClockAbstractEdge n) :
    clockAbstractChildPsi n r w e ≤ clockAbstractPsi n r w := by
  cases hs : clockAbstractStep n r w e with
  | none =>
    simp [clockAbstractChildPsi, hs]
  | some pair =>
    cases pair with
    | mk r' v =>
      simpa only [clockAbstractChildPsi, hs] using
        (clockAbstractEveryEdgeMono n hn r w e r' v hs)

/-- A strict abstract edge loses at least one ticket, including S1. -/
theorem clockAbstractChildStrict
    (n : Nat) (r : RootClass) (w : Nat → Fin 8)
    (e : ClockAbstractEdge n)
    (h : clockStrictEdge n r w e) :
    clockAbstractChildPsi n r w e + 1 ≤ clockAbstractPsi n r w := by
  cases hs : clockAbstractStep n r w e with
  | none =>
    simpa only [clockAbstractChildPsi, clockStrictEdge, hs,
      Nat.zero_add] using h
  | some pair =>
    cases pair with
    | mk r' v =>
      simpa only [clockAbstractChildPsi, clockStrictEdge, hs]
        using h

end L3


namespace L3

set_option autoImplicit false

/-!
Physical-transport foundation.
The following normalization is needed before any actual phiW
monotonicity or stopping-tree argument. Root C/F shape bytes
are irrelevant to Psi once the root certificate is RUNNING.
-/

/-- The physical clockwise shape word, as an infinite function.
    Only offsets below n are the actual ring's distinct sites. -/
def clockPhysicalShapeWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) : Nat → Fin 8 :=
  fun k => serShape (s (clockSite ring root k)).ser

theorem clockPhysicalShapeZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) :
    clockPhysicalShapeWord ring root s 0 =
      serShape (s root).ser := by
  simp only [clockPhysicalShapeWord, clockSiteZero]

/-- A B-phase serializer root has exactly its canonical B shape. -/
theorem clockSerBroadcastShape (s : Ser)
    (h : s.phase = .B) :
    serShape s = clockRootShape (rootClass s) := by
  cases ho : s.out <;>
    simp [serShape, rootClass, rootStage,
      clockRootShape, h, ho]

end L3

namespace L3

set_option autoImplicit false

/-- Exact normalization of Psi on a supplied word, where the
    physical shape at zero is the actual Ser's shape. This includes
    ROOT_IN's S6 case, whose C probe is intentionally left old. -/
theorem clockPsiNormalizeSer (n : Nat) (s : Ser)
    (w : Nat → Fin 8) (hzero : w 0 = serShape s) :
    startPsiWord n s.cert w =
      clockAbstractPsi n (rootClass s) w := by
  cases hc : s.cert with
  | IDLE =>
    simp [clockAbstractPsi, startPsiWord, rootClass, hc]
  | REQUESTED =>
    simp [clockAbstractPsi, startPsiWord, rootClass, hc]
  | RUNNING =>
    cases hp : s.phase with
    | B =>
      have hshape := clockSerBroadcastShape s hp
      have hword : clockAbstractWord (rootClass s) w = w := by
        funext k
        by_cases hk : k = 0
        · subst k
          change clockRootShape (rootClass s) = w 0
          exact hshape.symm.trans hzero.symm
        · simp [clockAbstractWord, hk]
      simpa only [clockAbstractPsi, rootClass, hc] using
        (congrArg (startPsiWord n .RUNNING) hword.symm)
    | C =>
      have hroot : (w 0).val ≤ 3 := by
        rw [hzero]
        cases hq : s.probe <;>
          simp [serShape, hp, hq] <;>
          decide
      have hh := clockPsiRunningNonB n w (Or.inl hroot)
      have hcanonical :
          clockAbstractPsi n (rootClass s) w = 3 := by
        simp [clockAbstractPsi, clockAbstractWord,
          rootClass, rootStage, clockRootShape,
          startPsiWord, hc, hp]
      calc
        startPsiWord n .RUNNING w = 3 := hh
        _ = clockAbstractPsi n (rootClass s) w :=
          hcanonical.symm
    | F =>
      have hroot : (w 0).val = 7 := by
        rw [hzero]
        simp [serShape, hp]
      have hh := clockPsiRunningNonB n w (Or.inr hroot)
      have hcanonical :
          clockAbstractPsi n (rootClass s) w = 3 := by
        simp [clockAbstractPsi, clockAbstractWord,
          rootClass, rootStage, clockRootShape,
          startPsiWord, hc, hp]
      calc
        startPsiWord n .RUNNING w = 3 := hh
        _ = clockAbstractPsi n (rootClass s) w :=
          hcanonical.symm

/-- The real startPsi equals the abstract word potential with its
    ROOT CLASS, including the C/F shape normalization at offset 0. -/
theorem clockStartPsiNormalize {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) :
    startPsi ring root s =
      clockAbstractPsi n (rootClass (s root).ser)
        (clockPhysicalShapeWord ring root s) := by
  change startPsiWord n (s root).ser.cert
      (clockPhysicalShapeWord ring root s) =
    clockAbstractPsi n (rootClass (s root).ser)
      (clockPhysicalShapeWord ring root s)
  exact clockPsiNormalizeSer n (s root).ser
    (clockPhysicalShapeWord ring root s)
    (clockPhysicalShapeZero ring root s)

/-- At a finite root-relative offset the new word is the same
    shape as the existing Fin-coordinate clockShapeAt. -/
theorem clockPhysicalShapeAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (k : Fin n) :
    clockPhysicalShapeWord ring root s k.val =
      clockShapeAt ring root s k := by
  rfl

/-- Any unselected, non-neighbor offset frames its actual shape. -/
theorem clockPhysicalShapeRemote {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e k : Fin n)
    (hk : k ≠ clockPosition ring root e)
    (hj : k ≠ ring.rightNeighbor (clockPosition ring root e)) :
    clockPhysicalShapeWord ring root (phiW ring s e) k.val =
      clockPhysicalShapeWord ring root s k.val := by
  simpa only [clockPhysicalShapeAt] using
    clockPhiRemoteOffset ring root s e k hk hj

/-- The abstract ROOT_OUT step is terminal exactly at
    a REQUESTED root, with no assumption on its B/C/F stage. -/
theorem clockRootOutNoneIff (r : RootClass) (y : Fin 8) :
    rootOut r y = none ↔ r.cert = .REQUESTED := by
  have ht := clockAbstractOutgoingTerminalIff 4 r (fun _ => y)
  constructor
  · intro h
    apply ht.mp
    simp [clockAbstractStep, h]
  · intro h
    exact rootOut_none_of_requested r y h

/-- The real ROOT_OUT S1 discriminator is the root certificate
    REQUESTED, as long as the selected successor has WFixedRoot. -/
theorem clockPhysicalSOneIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root)) :
    (serW (s root) (s (ring.rightNeighbor root))).row = "S1" ↔
      (s root).ser.cert = .REQUESTED := by
  have hrow :=
    clockPhiOutgoingTable ring root s root hn hfixed rfl
  have hnone := clockRootOutNoneIff
    (rootClass (s root).ser)
    (serShape (s (ring.rightNeighbor root)).ser)
  constructor
  · intro hs
    simp only [if_pos hs] at hrow
    exact hnone.mp hrow.symm
  · intro hc
    have hnrow : rootOut (rootClass (s root).ser)
        (serShape (s (ring.rightNeighbor root)).ser) = none :=
      hnone.mpr hc
    rw [hnrow] at hrow
    by_cases hs :
        (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
    · exact hs
    · simp only [if_neg hs] at hrow
      cases hrow

end L3


namespace L3

set_option autoImplicit false

/-!
First-n-offset locality for physical transport.

The physical clockwise word is periodic modulo n. The abstract
clockWrite is not. Their potentials can nevertheless agree when
all first n positions agree, because the terminal window branches
never inspect an out-of-range lookahead.
-/

/-- firstNonDone is determined by the finite scanned interval. -/
theorem clockFirstNonDoneIntervalExt (w v : Nat → Fin 8) :
    ∀ fuel start,
      (∀ i, start ≤ i → i < start + fuel → w i = v i) →
      firstNonDone w fuel start = firstNonDone v fuel start := by
  intro fuel
  induction fuel with
  | zero =>
    intro start _
    rfl
  | succ fuel ih =>
    intro start h
    have hhead : w start = v start :=
      h start (by omega) (by omega)
    change (if (w start).val = 6 then
      firstNonDone w fuel (start + 1) else start) =
      (if (v start).val = 6 then
      firstNonDone v fuel (start + 1) else start)
    rw [hhead]
    by_cases hd : (v start).val = 6
    · simp only [if_pos hd]
      apply ih (start + 1)
      intro i hlo hhi
      exact h i (by omega) (by omega)
    · simp [hd]

/-- The window remainder reads only offsets strictly below n.
    Its apparent w n / w (n+1) arguments are dead in terminal
    branches, including B/WAIT+PENDING at the last two sites. -/
theorem clockWindowPrefixExt
    (n k : Nat) (w v : Nat → Fin 8)
    (hk : k ≤ n)
    (hag : ∀ i, i < n → w i = v i) :
    clockWindowRemainder n k
      (w k) (w (k + 1)) (w (k + 2)) =
    clockWindowRemainder n k
      (v k) (v (k + 1)) (v (k + 2)) := by
  by_cases hkn : k = n
  · simp [clockWindowRemainder, hkn]
  · have hx : w k = v k := hag k (by omega)
    rw [hx]
    by_cases hlast : k + 1 = n
    · simp [clockWindowRemainder, hkn, hlast]
    · have hy : w (k + 1) = v (k + 1) :=
        hag (k + 1) (by omega)
      rw [hy]
      by_cases hnear : k + 2 = n
      · simp [clockWindowRemainder, hkn, hlast, hnear]
      · have hz : w (k + 2) = v (k + 2) :=
          hag (k + 2) (by omega)
        rw [hz]

/-- Exact all-n support locality of the start-clock potential.
    The root is included, so n must be nonzero. -/
theorem clockPsiPrefixExt
    (n : Nat) (hn : 0 < n) (cert : SerCert)
    (w v : Nat → Fin 8)
    (hag : ∀ i, i < n → w i = v i) :
    startPsiWord n cert w = startPsiWord n cert v := by
  cases cert with
  | IDLE =>
    rfl
  | REQUESTED =>
    rfl
  | RUNNING =>
    let k := firstNonDone w n 0
    have hk : firstNonDone w n 0 = k := rfl
    have hv : firstNonDone v n 0 = k := by
      dsimp [k]
      exact (clockFirstNonDoneIntervalExt w v n 0
        (by
          intro i _ hi
          exact hag i (by omega))).symm
    have hbound : k ≤ n := by
      have hh := (clockFirstNonDoneRange w n 0).2
      simpa only [Nat.zero_add, hk] using hh
    have hzero : w 0 = v 0 := hag 0 hn
    by_cases hr : (w 0).val ≤ 3 ∨ (w 0).val = 7
    · have hrV : (v 0).val ≤ 3 ∨ (v 0).val = 7 := by
        simpa only [hzero] using hr
      rw [clockPsiRunningNonB n w hr,
        clockPsiRunningNonB n v hrV]
    · have hrV : ¬ ((v 0).val ≤ 3 ∨ (v 0).val = 7) := by
        simpa only [hzero] using hr
      rw [clockPsiRunningWindow n k w hr hk,
        clockPsiRunningWindow n k v hrV hv]
      exact clockWindowPrefixExt n k w v hbound hag

end L3


namespace L3

set_option autoImplicit false

/-!
INTERNAL physical transport.
The selected physical sites are the root-relative offsets p,p+1.
Nonselected offsets are framed by clockPhiRemoteOffset. The
corresponding infinite words need agree only on the first n sites.
-/

/-- The two physical selected serializer shapes and all remote
    finite offsets equal their abstract INTERNAL table update.
    The root-exclusion premises are explicit in this lemma. -/
theorem clockPhysicalInternalPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root p : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hp : 0 < p.val) (hnext : p.val + 1 < n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p.val)))
    (he : clockSite ring root p.val ≠ root)
    (hj : ring.rightNeighbor
      (clockSite ring root p.val) ≠ root) :
    ∀ i : Nat, i < n →
      clockPhysicalShapeWord ring root
        (phiW ring s (clockSite ring root p.val)) i =
      clockInternalWord (clockPhysicalShapeWord ring root s)
        p.val i := by
  let e := clockSite ring root p.val
  let w := clockPhysicalShapeWord ring root s
  let v := clockPhysicalShapeWord ring root (phiW ring s e)
  have hsucc :
      ring.rightNeighbor p =
        (⟨p.val + 1, hnext⟩ : Fin n) := by
    apply Fin.ext
    change (p.val + 1) % n = p.val + 1
    exact Nat.mod_eq_of_lt hnext
  have hpair :
      (v p.val, v (p.val + 1)) =
        followerPair (w p.val) (w (p.val + 1)) := by
    have ht := clockPhiInternalOffset ring root p s
      (by omega : 2 ≤ n) hfixed he hj
    rw [hsucc] at ht
    change (v p.val, v (p.val + 1)) =
      followerPair (w p.val) (w (p.val + 1)) at ht
    exact ht
  have hsource :
      v p.val = (followerPair (w p.val) (w (p.val + 1))).1 :=
    congrArg Prod.fst hpair
  have htarget :
      v (p.val + 1) =
        (followerPair (w p.val) (w (p.val + 1))).2 :=
    congrArg Prod.snd hpair
  intro i hi
  by_cases hpi : i = p.val
  · subst i
    change v p.val = clockInternalWord w p.val p.val
    rw [clockInternalWordSource]
    exact hsource
  · by_cases hji : i = p.val + 1
    · subst i
      change v (p.val + 1) =
        clockInternalWord w p.val (p.val + 1)
      rw [clockInternalWordTarget]
      exact htarget
    · have hpos :
          (⟨i, hi⟩ : Fin n) ≠ p := by
        intro hh
        exact hpi (congrArg Fin.val hh)
      have hposNext :
          (⟨i, hi⟩ : Fin n) ≠ ring.rightNeighbor p := by
        intro hh
        have hv := congrArg Fin.val hh
        rw [hsucc] at hv
        exact hji hv
      have hremSource :
          (⟨i, hi⟩ : Fin n) ≠
            clockPosition ring root e := by
        change (⟨i, hi⟩ : Fin n) ≠
          clockPosition ring root (clockSite ring root p.val)
        simpa only [clockPositionSite] using hpos
      have hremTarget :
          (⟨i, hi⟩ : Fin n) ≠
            ring.rightNeighbor (clockPosition ring root e) := by
        change (⟨i, hi⟩ : Fin n) ≠
          ring.rightNeighbor
            (clockPosition ring root (clockSite ring root p.val))
        simpa only [clockPositionSite] using hposNext
      have hframe : v i = w i := by
        simpa only [] using
          (clockPhysicalShapeRemote ring root s e
            (⟨i, hi⟩ : Fin n) hremSource hremTarget)
      have habs : clockInternalWord w p.val i = w i :=
        clockInternalWordRemote w p.val i hpi hji
      exact hframe.trans habs.symm

/-- Conditional weak monotonicity of one actual physical INTERNAL
    step. The hfixed input is on the SUCCESSOR, as demanded by
    the original WOriginHistory.next constructor. -/
theorem clockPhiInternalPsiWeak {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root p : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hp : 0 < p.val) (hnext : p.val + 1 < n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p.val)))
    (he : clockSite ring root p.val ≠ root)
    (hj : ring.rightNeighbor
      (clockSite ring root p.val) ≠ root) :
    startPsi ring root
        (phiW ring s (clockSite ring root p.val)) ≤
      startPsi ring root s := by
  let e := clockSite ring root p.val
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  let v := clockPhysicalShapeWord ring root (phiW ring s e)
  have hser :
      ((phiW ring s e) root).ser = (s root).ser :=
    phiW_ser_remote ring s e root he.symm hj.symm
  have hclass :
      rootClass ((phiW ring s e) root).ser = r :=
    congrArg rootClass hser
  have hprefix :
      ∀ i, i < n → v i = clockInternalWord w p.val i :=
    clockPhysicalInternalPrefix ring root p s
      hn hp hnext hfixed he hj
  have hclock :
      clockAbstractPsi n r v =
        clockAbstractPsi n r (clockInternalWord w p.val) := by
    change startPsiWord n r.cert (clockAbstractWord r v) =
      startPsiWord n r.cert
        (clockAbstractWord r (clockInternalWord w p.val))
    apply clockPsiPrefixExt n (by omega) r.cert
    intro i hi
    by_cases hz : i = 0
    · simp [clockAbstractWord, hz]
    · have ht := hprefix i hi
      simpa only [clockAbstractWord, if_neg hz] using ht
  rw [clockStartPsiNormalize ring root
      (phiW ring s (clockSite ring root p.val)),
    clockStartPsiNormalize ring root s]
  rw [hclass]
  change clockAbstractPsi n r v ≤ clockAbstractPsi n r w
  calc
    clockAbstractPsi n r v =
        clockAbstractPsi n r (clockInternalWord w p.val) := hclock
    _ ≤ clockAbstractPsi n r w :=
      clockAbstractInternalMono n hn r w p.val hp hnext

end L3


namespace L3

set_option autoImplicit false

/-!
Physical seam geometry and selected tables.
The source-root is offset zero, its
right neighbor offset one, and the predecessor offset n-1.
-/

/-- The physical root occupies root-relative offset zero. -/
theorem clockPositionRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 0 < n) :
    clockPosition ring root root =
      (⟨0, hn⟩ : Fin n) := by
  have hh := clockPositionSite ring root (⟨0, hn⟩ : Fin n)
  rw [clockSiteZero] at hh
  exact hh

/-- The root's outgoing physical responder occupies offset one. -/
theorem clockSiteOne {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n) :
    clockSite ring root 1 = ring.rightNeighbor root := by
  have hh := clockSiteNext ring root (⟨0, by omega⟩ : Fin n)
  have hs :
      ring.rightNeighbor (⟨0, by omega⟩ : Fin n) =
      (⟨1, by omega⟩ : Fin n) := by
    apply Fin.ext
    change (0 + 1) % n = 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [hs, clockSiteZero] at hh
  exact hh

/-- The incoming physical source at offset n-1 points to root. -/
theorem clockSiteLast {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n) :
    ring.rightNeighbor (clockSite ring root (n - 1)) = root := by
  have hh := clockSiteNext ring root
    (⟨n - 1, by omega⟩ : Fin n)
  have hs :
      ring.rightNeighbor (⟨n - 1, by omega⟩ : Fin n) =
      (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    change (n - 1 + 1) % n = 0
    rw [show n - 1 + 1 = n from by omega, Nat.mod_self]
  rw [hs, clockSiteZero] at hh
  exact hh.symm

/-- ROOT_OUT's true physical serializer row in abstract
    word-coordinates, including the none=S1 terminal branch. -/
theorem clockPhysicalOutgoingSelected {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root)) :
    (if (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
     then none
     else some
       (rootClass ((phiW ring s root) root).ser,
        clockPhysicalShapeWord ring root (phiW ring s root) 1)) =
    rootOut (rootClass (s root).ser)
      (clockPhysicalShapeWord ring root s 1) := by
  have ht := clockPhiOutgoingTable ring root s root
    hn hfixed rfl
  simpa only [clockPhysicalShapeWord,
    clockSiteOne ring root hn] using ht

/-- ROOT_IN's selected physical serializer pair at offset n-1
    and at the root, with successor WFixedRoot as premise. -/
theorem clockPhysicalIncomingSelected {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root (n - 1)))) :
    (clockPhysicalShapeWord ring root
       (phiW ring s (clockSite ring root (n - 1))) (n - 1),
     rootClass ((phiW ring s
       (clockSite ring root (n - 1))) root).ser) =
    rootIn (clockPhysicalShapeWord ring root s (n - 1))
      (rootClass (s root).ser) := by
  let p : Fin n := ⟨n - 1, by omega⟩
  have hlast :
      ring.rightNeighbor (clockSite ring root p.val) = root := by
    simpa only [p] using clockSiteLast ring root hn
  have ht := clockPhiIncomingOffset ring root p s
    hn hfixed hlast
  change
    (clockShapeAt ring root
      (phiW ring s (clockSite ring root p.val)) p,
     rootClass ((phiW ring s
       (clockSite ring root p.val)) root).ser) =
      rootIn (clockShapeAt ring root s p)
        (rootClass (s root).ser)
  exact ht

end L3


namespace L3

set_option autoImplicit false

/-!
Nonterminal physical ROOT_OUT transport.
The root-class response is obtained directly from the
clockPhiOutgoingTable, and every follower except offset one
is framed using clockPhysicalShapeRemote.
-/

/-- The successor of root-relative offset zero is offset one. -/
theorem clockPositionRootNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n) :
    ring.rightNeighbor (clockPosition ring root root) =
      (⟨1, by omega⟩ : Fin n) := by
  rw [clockPositionRoot ring root (by omega)]
  apply Fin.ext
  change (0 + 1) % n = 1
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- A physical ROOT_OUT non-S1 step is exactly the abstract
    rootOut row on the root class and first follower; every
    other follower offset is an exact serializer frame. -/
theorem clockPhysicalOutgoingPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (hnotSOne :
      (serW (s root) (s (ring.rightNeighbor root))).row ≠ "S1") :
    ∃ (r' : RootClass) (y : Fin 8),
      rootOut (rootClass (s root).ser)
        (clockPhysicalShapeWord ring root s 1) = some (r', y) ∧
      rootClass ((phiW ring s root) root).ser = r' ∧
      ∀ i, i < n → 0 < i →
        clockPhysicalShapeWord ring root (phiW ring s root) i =
          clockWrite (clockPhysicalShapeWord ring root s) 1 y i := by
  have ht := clockPhysicalOutgoingSelected ring root s
    (by omega : 2 ≤ n) hfixed
  simp only [if_neg hnotSOne] at ht
  refine ⟨rootClass ((phiW ring s root) root).ser,
    clockPhysicalShapeWord ring root (phiW ring s root) 1,
    ht.symm, rfl, ?_⟩
  intro i hi hpos
  by_cases hfirst : i = 1
  · subst i
    simp [clockWriteAtSite]
  · have hposRoot :
        clockPosition ring root root =
          (⟨0, by omega⟩ : Fin n) :=
      clockPositionRoot ring root (by omega)
    have hposNext :
        ring.rightNeighbor (clockPosition ring root root) =
          (⟨1, by omega⟩ : Fin n) :=
      clockPositionRootNext ring root (by omega)
    have hneRoot :
        (⟨i, hi⟩ : Fin n) ≠ clockPosition ring root root := by
      rw [hposRoot]
      intro hh
      have hv := congrArg Fin.val hh
      change i = 0 at hv
      omega
    have hneNext :
        (⟨i, hi⟩ : Fin n) ≠
          ring.rightNeighbor (clockPosition ring root root) := by
      rw [hposNext]
      intro hh
      have hv := congrArg Fin.val hh
      change i = 1 at hv
      exact hfirst hv
    have hframe :=
      clockPhysicalShapeRemote ring root s root
        (⟨i, hi⟩ : Fin n) hneRoot hneNext
    calc
      clockPhysicalShapeWord ring root (phiW ring s root) i =
          clockPhysicalShapeWord ring root s i := by
            simpa only [] using hframe
      _ = clockWrite (clockPhysicalShapeWord ring root s) 1
            (clockPhysicalShapeWord ring root (phiW ring s root) 1)
            i := (clockWriteOtherSite _ 1 i _ hfirst).symm

/-- Every physical nonterminal ROOT_OUT step weakly decreases
    the exact startPsi, assuming WFixedRoot of its successor. -/
theorem clockPhiOutgoingPsiWeak {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (hnotSOne :
      (serW (s root) (s (ring.rightNeighbor root))).row ≠ "S1") :
    startPsi ring root (phiW ring s root) ≤
      startPsi ring root s := by
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  let v := clockPhysicalShapeWord ring root (phiW ring s root)
  obtain ⟨r', y, hrow, hclass, hframe⟩ :=
    clockPhysicalOutgoingPrefix ring root s hn hfixed hnotSOne
  have hc : r.cert ≠ .REQUESTED := by
    intro hreq
    apply hnotSOne
    exact (clockPhysicalSOneIff ring root s
      (by omega : 2 ≤ n) hfixed).2 hreq
  have hlocal :
      clockAbstractPsi n r' v =
        clockAbstractPsi n r' (clockWrite w 1 y) := by
    change startPsiWord n r'.cert (clockAbstractWord r' v) =
      startPsiWord n r'.cert
        (clockAbstractWord r' (clockWrite w 1 y))
    apply clockPsiPrefixExt n (by omega) r'.cert
    intro i hi
    by_cases hz : i = 0
    · simp [clockAbstractWord, hz]
    · have h := hframe i hi (by omega)
      simpa only [clockAbstractWord, if_neg hz] using h
  rw [clockStartPsiNormalize ring root (phiW ring s root),
    clockStartPsiNormalize ring root s]
  rw [hclass]
  change clockAbstractPsi n r' v ≤ clockAbstractPsi n r w
  calc
    clockAbstractPsi n r' v =
        clockAbstractPsi n r' (clockWrite w 1 y) := hlocal
    _ ≤ clockAbstractPsi n r w :=
      clockRootOutNonSOneMono n hn r w r' y hc hrow

end L3


namespace L3

set_option autoImplicit false

/-!
Physical ROOT_IN transport.
Only the last follower and root are selected, with the new
root class obtained from clockPhiIncomingOffset.
-/

/-- The root's predecessor is the final clockwise Fin offset,
    whose right neighbor is the zero offset. -/
theorem clockLastPositionRightZero {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) :
    ring.rightNeighbor (⟨n - 1, by omega⟩ : Fin n) =
      (⟨0, by omega⟩ : Fin n) := by
  apply Fin.ext
  change (n - 1 + 1) % n = 0
  rw [show n - 1 + 1 = n from by omega, Nat.mod_self]

/-- ROOT_IN selected pair plus the exact remote frame at every
    positive follower offset. No initial WFixedRoot assumption. -/
theorem clockPhysicalIncomingPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root (n - 1)))) :
    ∃ (r' : RootClass) (x : Fin 8),
      rootIn (clockPhysicalShapeWord ring root s (n - 1))
        (rootClass (s root).ser) = (x, r') ∧
      rootClass ((phiW ring s
        (clockSite ring root (n - 1))) root).ser = r' ∧
      ∀ i, i < n → 0 < i →
        clockPhysicalShapeWord ring root
          (phiW ring s (clockSite ring root (n - 1))) i =
          clockWrite (clockPhysicalShapeWord ring root s)
            (n - 1) x i := by
  let e := clockSite ring root (n - 1)
  let w := clockPhysicalShapeWord ring root s
  let v := clockPhysicalShapeWord ring root (phiW ring s e)
  have ht := clockPhysicalIncomingSelected ring root s
    (by omega : 2 ≤ n) hfixed
  refine ⟨rootClass ((phiW ring s e) root).ser,
    v (n - 1), ?_, rfl, ?_⟩
  · exact ht.symm
  · intro i hi hpos
    by_cases hlast : i = n - 1
    · subst i
      simp [clockWriteAtSite]
      rfl
    · let p : Fin n := ⟨n - 1, by omega⟩
      have hposLast :
          clockPosition ring root e = p := by
        change clockPosition ring root
          (clockSite ring root p.val) = p
        exact clockPositionSite ring root p
      have hright :
          ring.rightNeighbor p = (⟨0, by omega⟩ : Fin n) := by
        simpa only [p] using clockLastPositionRightZero ring
          (by omega : 2 ≤ n)
      have hneSource :
          (⟨i, hi⟩ : Fin n) ≠ clockPosition ring root e := by
        rw [hposLast]
        intro hh
        have hv := congrArg Fin.val hh
        change i = n - 1 at hv
        exact hlast hv
      have hneTarget :
          (⟨i, hi⟩ : Fin n) ≠
            ring.rightNeighbor (clockPosition ring root e) := by
        rw [hposLast, hright]
        intro hh
        have hv := congrArg Fin.val hh
        change i = 0 at hv
        omega
      have hframe : v i = w i := by
        simpa only [] using
          (clockPhysicalShapeRemote ring root s e
            (⟨i, hi⟩ : Fin n) hneSource hneTarget)
      exact hframe.trans
        (clockWriteOtherSite w (n - 1) i (v (n - 1)) hlast).symm

/-- Every actual ROOT_IN step weakly decreases the physical
    startPsi under its successor WFixedRoot hypothesis. -/
theorem clockPhiIncomingPsiWeak {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root (n - 1)))) :
    startPsi ring root
      (phiW ring s (clockSite ring root (n - 1))) ≤
    startPsi ring root s := by
  let e := clockSite ring root (n - 1)
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  let v := clockPhysicalShapeWord ring root (phiW ring s e)
  obtain ⟨r', x, hrow, hclass, hframe⟩ :=
    clockPhysicalIncomingPrefix ring root s hn hfixed
  have hlocal :
      clockAbstractPsi n r' v =
        clockAbstractPsi n r' (clockWrite w (n - 1) x) := by
    change startPsiWord n r'.cert (clockAbstractWord r' v) =
      startPsiWord n r'.cert
        (clockAbstractWord r' (clockWrite w (n - 1) x))
    apply clockPsiPrefixExt n (by omega) r'.cert
    intro i hi
    by_cases hz : i = 0
    · simp [clockAbstractWord, hz]
    · have hh := hframe i hi (by omega)
      simpa only [clockAbstractWord, if_neg hz] using hh
  have habstract :
      clockAbstractPsi n r' (clockWrite w (n - 1) x) ≤
        clockAbstractPsi n r w := by
    have hm := clockRootInMono n hn r w
    rw [hrow] at hm
    exact hm
  rw [clockStartPsiNormalize ring root
      (phiW ring s (clockSite ring root (n - 1))),
    clockStartPsiNormalize ring root s]
  rw [hclass]
  change clockAbstractPsi n r' v ≤ clockAbstractPsi n r w
  exact Nat.le_trans (Nat.le_of_eq hlocal) habstract

end L3


namespace L3

set_option autoImplicit false

/-!
Weak physical all-edge assembly.
The sole excluded event is ROOT_OUT/S1, whose proper stopped
successor is a terminal marker rather than the continued phiW cut.
-/

/-- Any positive non-root offset is physically distinct from the
    fixed root, by injectivity of clockwise ring coordinates. -/
theorem clockInternalSiteNotRoot {n : Nat}
    (ring : DirectedRing n) (root p : Fin n)
    (hn : 4 ≤ n) (hp : 0 < p.val) :
    clockSite ring root p.val ≠ root := by
  intro h
  have hz :
      clockSite ring root p.val = clockSite ring root 0 :=
    h.trans (clockSiteZero ring root).symm
  have hh := clockSiteInjective ring root p
    (⟨0, by omega⟩ : Fin n) hz
  have hv : p.val = 0 := by
    simpa only [Fin.val_mk] using congrArg Fin.val hh
  omega

/-- An internal edge whose next offset is below n also has a
    non-root responder. -/
theorem clockInternalNextNotRoot {n : Nat}
    (ring : DirectedRing n) (root p : Fin n)
    (hn : 4 ≤ n) (hnext : p.val + 1 < n) :
    ring.rightNeighbor (clockSite ring root p.val) ≠ root := by
  intro h
  have hshift := clockSiteNext ring root p
  have hz :
      clockSite ring root (ring.rightNeighbor p).val =
        clockSite ring root 0 :=
    (hshift.trans h).trans (clockSiteZero ring root).symm
  have hh := clockSiteInjective ring root
    (ring.rightNeighbor p) (⟨0, by omega⟩ : Fin n) hz
  have hv : (ring.rightNeighbor p).val = 0 := by
    simpa only [Fin.val_mk] using congrArg Fin.val hh
  have hval : (ring.rightNeighbor p).val = p.val + 1 := by
    change (p.val + 1) % n = p.val + 1
    exact Nat.mod_eq_of_lt hnext
  omega

/-- Every genuine physical successor preserving WFixedRoot
    weakly decreases Psi, provided the selected edge is not S1.
    The edge classification is done by clockPosition and the
    modulo-n root-relative geometry. -/
theorem clockPhiEveryNonterminalPsiWeak {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hnon :
      e = root →
      (serW (s root) (s (ring.rightNeighbor root))).row ≠ "S1") :
    startPsi ring root (phiW ring s e) ≤
      startPsi ring root s := by
  let p := clockPosition ring root e
  have hsite : clockSite ring root p.val = e :=
    clockSitePosition ring root e
  by_cases hzero : p.val = 0
  · have he : e = root := by
      calc
        e = clockSite ring root p.val := hsite.symm
        _ = clockSite ring root 0 := by rw [hzero]
        _ = root := clockSiteZero ring root
    have hfixRoot : WFixedRoot ring root (phiW ring s root) := by
      simpa only [he] using hfixed
    have hh := clockPhiOutgoingPsiWeak ring root s
      hn hfixRoot (hnon he)
    simpa only [he] using hh
  · by_cases hlast : p.val = n - 1
    · have hsiteLast : clockSite ring root (n - 1) = e := by
        calc
          clockSite ring root (n - 1) =
              clockSite ring root p.val := by rw [hlast]
          _ = e := hsite
      have hfixLast :
          WFixedRoot ring root
            (phiW ring s (clockSite ring root (n - 1))) := by
        simpa only [hsiteLast] using hfixed
      have hh := clockPhiIncomingPsiWeak ring root s
        hn hfixLast
      simpa only [hsiteLast] using hh
    · have hp : 0 < p.val := by
        have hlt := p.isLt
        omega
      have hnext : p.val + 1 < n := by
        have hlt := p.isLt
        omega
      have he := clockInternalSiteNotRoot ring root p hn hp
      have hj := clockInternalNextNotRoot ring root p hn hnext
      have hfixInternal :
          WFixedRoot ring root
            (phiW ring s (clockSite ring root p.val)) := by
        simpa only [hsite] using hfixed
      have hh := clockPhiInternalPsiWeak ring root p s
        hn hp hnext hfixInternal he hj
      simpa only [hsite] using hh

end L3


namespace L3

set_option autoImplicit false

/-!
All-n initial potential cap.
The only apparently larger row is a C frontier at k=0;
this cannot arise from a RUNNING B root, so k>0 is
a structural hypothesis in the general window inequality.
-/

/-- Uniform thirteen-row window bound, including the terminal
    k=n, k+1=n and k+2=n cases. -/
theorem clockWindowCap
    (n k : Nat) (hn : 4 ≤ n) (hk : k ≤ n)
    (x y z : Fin 8)
    (hfront : 0 < k ∨ 4 ≤ x.val) :
    clockWindowRemainder n k x y z ≤ 5 * n - 4 := by
  by_cases hkn : k = n
  · simp [clockWindowRemainder, hkn] <;> omega
  · by_cases hf : x.val = 7
    · simp [clockWindowRemainder, hkn, hf] <;> omega
    · by_cases hc : x.val ≤ 3
      · have hkpos : 0 < k := by
          rcases hfront with hp | hx
          · exact hp
          · omega
        by_cases hlast : k + 1 = n
        · simp [clockWindowRemainder, hkn, hf, hc, hlast] <;> omega
        · simp [clockWindowRemainder, hkn, hf, hc, hlast] <;> omega
      · by_cases hnew : x.val = 4
        · by_cases hlast : k + 1 = n
          · simp [clockWindowRemainder, hkn, hf, hc, hnew, hlast] <;> omega
          · simp [clockWindowRemainder, hkn, hf, hc, hnew, hlast] <;> omega
        · by_cases hwait : x.val = 5
          · by_cases hlast : k + 1 = n
            · simp [clockWindowRemainder, hkn, hf, hc, hnew, hwait, hlast] <;> omega
            · by_cases hpending : y.val = 1
              · by_cases hnear : k + 2 = n
                · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                    hwait, hlast, hpending, hnear] <;> omega
                · by_cases hhigh : 4 ≤ z.val
                  · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                      hwait, hlast, hpending, hnear, hhigh] <;> omega
                  · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                      hwait, hlast, hpending, hnear, hhigh] <;> omega
              · by_cases hinternal : y.val = 2
                · by_cases hnear : k + 2 = n
                  · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                      hwait, hlast, hpending, hinternal, hnear] <;> omega
                  · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                      hwait, hlast, hpending, hinternal, hnear] <;> omega
                · by_cases hleaf : y.val = 3
                  · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                      hwait, hlast, hpending, hinternal, hleaf] <;> omega
                  · by_cases hnear : k + 2 = n
                    · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                        hwait, hlast, hpending, hinternal, hleaf, hnear] <;> omega
                    · simp [clockWindowRemainder, hkn, hf, hc, hnew,
                        hwait, hlast, hpending, hinternal, hleaf, hnear] <;> omega
          · simp [clockWindowRemainder, hkn, hf, hc, hnew, hwait] <;> omega

/-- The abstract start-clock potential is at most 5n-4 in
    every root class and for every Cartesian follower word. -/
theorem clockAbstractPsiCap
    (n : Nat) (hn : 4 ≤ n)
    (r : RootClass) (w : Nat → Fin 8) :
    clockAbstractPsi n r w ≤ 5 * n - 4 := by
  cases hc : r.cert with
  | IDLE =>
    rw [show clockAbstractPsi n r w = 2 from by
      simp [clockAbstractPsi, rootClass, startPsiWord, hc]]
    omega
  | REQUESTED =>
    rw [show clockAbstractPsi n r w = 1 from by
      simp [clockAbstractPsi, rootClass, startPsiWord, hc]]
    omega
  | RUNNING =>
    by_cases hs : r.stage = .nonB
    · have hvalue : clockAbstractPsi n r w = 3 := by
        simp [clockAbstractPsi, clockAbstractWord,
          clockRootShape, startPsiWord, hc, hs]
      rw [hvalue]
      omega
    · let u := clockAbstractWord r w
      let k := firstNonDone u n 0
      have hfirst : firstNonDone u n 0 = k := rfl
      have hbound : k ≤ n := by
        have hh := (clockFirstNonDoneRange u n 0).2
        simpa only [Nat.zero_add] using hh
      have hrootHigh : 4 ≤ (u 0).val := by
        cases ht : r.stage with
        | nonB =>
          exact False.elim (hs ht)
        | freshB =>
          simp [u, clockAbstractWord, clockRootShape, ht]
        | waitingB =>
          simp [u, clockAbstractWord, clockRootShape, ht]
        | completedB =>
          simp [u, clockAbstractWord, clockRootShape, ht]
      have hfront : 0 < k ∨ 4 ≤ (u k).val := by
        by_cases hz : k = 0
        · right
          rw [hz]
          exact hrootHigh
        · left
          omega
      have hwindow :=
        clockWindowCap n k hn hbound
          (u k) (u (k + 1)) (u (k + 2)) hfront
      have heq := clockRootRunningRemainder n k r w
        hc hs hfirst
      rw [heq]
      exact hwindow

/-- Consequently the real physical startPsi has the same cap. -/
theorem clockStartPsiCap {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) :
    startPsi ring root s ≤ 5 * n - 4 := by
  rw [clockStartPsiNormalize ring root s]
  exact clockAbstractPsiCap n hn
    (rootClass (s root).ser) (clockPhysicalShapeWord ring root s)

end L3


namespace L3

set_option autoImplicit false

/-!
Exact stopped-child transport.
The successor WFixedRoot premise is retained explicitly.
-/

/-- The canonical root shape is fixed by RootClass, so physical
    follower agreement below n suffices for Psi equality. -/
theorem clockAbstractPsiPositivePrefix
    (n : Nat) (hn : 0 < n)
    (r : RootClass) (u v : Nat → Fin 8)
    (h : ∀ i, i < n → 0 < i → u i = v i) :
    clockAbstractPsi n r u = clockAbstractPsi n r v := by
  change startPsiWord n r.cert (clockAbstractWord r u) =
    startPsiWord n r.cert (clockAbstractWord r v)
  apply clockPsiPrefixExt n hn r.cert
  intro i hi
  by_cases hz : i = 0
  · subst i
    rfl
  · simpa only [clockAbstractWord, if_neg hz] using
      h i hi (by omega)

/-- An INTERNAL physical successor has exactly the abstract
    INTERNAL potential, not merely an upper bound. -/
theorem clockPhiInternalPsiExact {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (s : Fin n → ProjW c)
    (hn : 4 ≤ n) (hp : 0 < p) (hnext : p + 1 < n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root p))) :
    startPsi ring root (phiW ring s (clockSite ring root p)) =
      clockAbstractPsi n (rootClass (s root).ser)
        (clockInternalWord (clockPhysicalShapeWord ring root s) p) := by
  let q : Fin n := ⟨p, by omega⟩
  have hq : q.val = p := rfl
  have hposQ : 0 < q.val := by
    rw [hq]
    exact hp
  have hnextQ : q.val + 1 < n := by
    rw [hq]
    exact hnext
  have he := clockInternalSiteNotRoot ring root q hn hposQ
  have hj := clockInternalNextNotRoot ring root q hn hnextQ
  have hprefix := clockPhysicalInternalPrefix ring root q s
    hn hposQ hnextQ hfixed he hj
  have hser :
      ((phiW ring s (clockSite ring root p)) root).ser =
        (s root).ser :=
    phiW_ser_remote ring s (clockSite ring root p)
      root he.symm hj.symm
  have hclass :
      rootClass ((phiW ring s
        (clockSite ring root p)) root).ser =
        rootClass (s root).ser :=
    congrArg rootClass hser
  rw [clockStartPsiNormalize ring root
    (phiW ring s (clockSite ring root p)), hclass]
  apply clockAbstractPsiPositivePrefix n (by omega)
  intro i hi _
  exact hprefix i hi

/-- Exact ROOT_OUT successor potential in the non-S1 branch. -/
theorem clockPhiOutgoingPsiExact {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (hnotSOne :
      (serW (s root) (s (ring.rightNeighbor root))).row ≠ "S1") :
    ∃ (r' : RootClass) (y : Fin 8),
      rootOut (rootClass (s root).ser)
        (clockPhysicalShapeWord ring root s 1) = some (r', y) ∧
      startPsi ring root (phiW ring s root) =
        clockAbstractPsi n r'
          (clockWrite (clockPhysicalShapeWord ring root s) 1 y) := by
  obtain ⟨r', y, hrow, hclass, hframe⟩ :=
    clockPhysicalOutgoingPrefix ring root s hn hfixed hnotSOne
  refine ⟨r', y, hrow, ?_⟩
  rw [clockStartPsiNormalize ring root (phiW ring s root), hclass]
  exact clockAbstractPsiPositivePrefix n (by omega) r'
    (clockPhysicalShapeWord ring root (phiW ring s root))
    (clockWrite (clockPhysicalShapeWord ring root s) 1 y)
    hframe

/-- Exact ROOT_IN successor potential, with the updated RootClass
    taken from the actual incoming S0/S5 table. -/
theorem clockPhiIncomingPsiExact {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockSite ring root (n - 1)))) :
    ∃ (r' : RootClass) (x : Fin 8),
      rootIn (clockPhysicalShapeWord ring root s (n - 1))
        (rootClass (s root).ser) = (x, r') ∧
      startPsi ring root
        (phiW ring s (clockSite ring root (n - 1))) =
      clockAbstractPsi n r'
        (clockWrite (clockPhysicalShapeWord ring root s)
          (n - 1) x) := by
  obtain ⟨r', x, hrow, hclass, hframe⟩ :=
    clockPhysicalIncomingPrefix ring root s hn hfixed
  refine ⟨r', x, hrow, ?_⟩
  rw [clockStartPsiNormalize ring root
    (phiW ring s (clockSite ring root (n - 1))), hclass]
  exact clockAbstractPsiPositivePrefix n (by omega) r'
    (clockPhysicalShapeWord ring root
      (phiW ring s (clockSite ring root (n - 1))))
    (clockWrite (clockPhysicalShapeWord ring root s) (n - 1) x)
    hframe

/-- Identify an abstract edge with its actual physical source
    in clockwise ring coordinates. -/
def clockPhysicalEdgeOfAbstract {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ClockAbstractEdge n → Fin n
  | .internal p _ _ => clockSite ring root p
  | .outgoing => root
  | .incoming => clockSite ring root (n - 1)

/-- S1 is an event terminal, not a continued phiW state: assign
    potential zero at its selected service and physical Psi elsewhere. -/
def clockPhysicalStoppedChildPsi {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) : Nat :=
  if e = root ∧
      (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
  then 0
  else startPsi ring root (phiW ring s e)

/-- Exact equality of an abstract stopped child and its physical
    source service, under the successor WFixedRoot hypothesis. -/
theorem clockPhysicalStoppedChildTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n)
    (edge : ClockAbstractEdge n)
    (hfixed : WFixedRoot ring root
      (phiW ring s (clockPhysicalEdgeOfAbstract ring root edge))) :
    clockPhysicalStoppedChildPsi ring root s
        (clockPhysicalEdgeOfAbstract ring root edge) =
      clockAbstractChildPsi n (rootClass (s root).ser)
        (clockPhysicalShapeWord ring root s) edge := by
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  cases edge with
  | internal p hp hnext =>
    let q : Fin n := ⟨p, by omega⟩
    have hne : clockSite ring root p ≠ root :=
      clockInternalSiteNotRoot ring root q hn (by
        change 0 < p
        exact hp)
    have hnot :
        ¬ (clockSite ring root p = root ∧
          (serW (s root) (s (ring.rightNeighbor root))).row = "S1") := by
      intro h
      exact hne h.1
    have hEq := clockPhiInternalPsiExact ring root p s
      hn hp hnext hfixed
    change
      (if clockSite ring root p = root ∧
          (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
       then 0 else startPsi ring root
         (phiW ring s (clockSite ring root p))) =
      clockAbstractPsi n r (clockInternalWord w p)
    rw [if_neg hnot]
    exact hEq
  | outgoing =>
    by_cases hs :
        (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
    · have hc : r.cert = .REQUESTED := by
        change (s root).ser.cert = .REQUESTED
        exact (clockPhysicalSOneIff ring root s
          (by omega : 2 ≤ n) hfixed).1 hs
      have hnone : clockAbstractStep n r w .outgoing = none :=
        (clockAbstractOutgoingTerminalIff n r w).2 hc
      have hstop :
          root = root ∧
            (serW (s root) (s (ring.rightNeighbor root))).row = "S1" :=
        ⟨rfl, hs⟩
      change
        (if root = root ∧
            (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
         then 0 else startPsi ring root (phiW ring s root)) =
        (match clockAbstractStep n r w .outgoing with
        | none => 0
        | some (r', v) => clockAbstractPsi n r' v)
      rw [if_pos hstop, hnone]
    · obtain ⟨r', y, hrow, hEq⟩ :=
        clockPhiOutgoingPsiExact ring root s hn hfixed hs
      have hstep :
          clockAbstractStep n r w .outgoing =
            some (r', clockWrite w 1 y) := by
        change
          (match rootOut r (w 1) with
          | none => none
          | some (r0, y0) => some (r0, clockWrite w 1 y0)) =
            some (r', clockWrite w 1 y)
        rw [hrow]
      have hnot :
          ¬ (root = root ∧
            (serW (s root) (s (ring.rightNeighbor root))).row = "S1") := by
        intro h
        exact hs h.2
      change
        (if root = root ∧
            (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
         then 0 else startPsi ring root (phiW ring s root)) =
        (match clockAbstractStep n r w .outgoing with
        | none => 0
        | some (r0, v0) => clockAbstractPsi n r0 v0)
      rw [if_neg hnot, hstep]
      exact hEq
  | incoming =>
    have hne : clockSite ring root (n - 1) ≠ root :=
      clockInternalSiteNotRoot ring root
        (⟨n - 1, by omega⟩ : Fin n) hn (by
          change 0 < n - 1
          omega)
    obtain ⟨r', x, hrow, hEq⟩ :=
      clockPhiIncomingPsiExact ring root s hn hfixed
    have hstep :
        clockAbstractStep n r w .incoming =
          some (r', clockWrite w (n - 1) x) := by
      change
        some ((rootIn (w (n - 1)) r).2,
          clockWrite w (n - 1) (rootIn (w (n - 1)) r).1) =
        some (r', clockWrite w (n - 1) x)
      rw [hrow]
    have hnot :
        ¬ (clockSite ring root (n - 1) = root ∧
          (serW (s root) (s (ring.rightNeighbor root))).row = "S1") := by
      intro h
      exact hne h.1
    change
      (if clockSite ring root (n - 1) = root ∧
          (serW (s root) (s (ring.rightNeighbor root))).row = "S1"
       then 0 else startPsi ring root
         (phiW ring s (clockSite ring root (n - 1)))) =
      (match clockAbstractStep n r w .incoming with
      | none => 0
      | some (r0, v0) => clockAbstractPsi n r0 v0)
    rw [if_neg hnot, hstep]
    exact hEq

/-- Conditional strict physical nomination: one genuine ring
    service loses a full Psi ticket, counting S1 as zero. -/
theorem clockPhysicalNominatedStrict {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n)
    (hfixed : ∀ e : Fin n, WFixedRoot ring root (phiW ring s e)) :
    ∃ e : Fin n,
      clockPhysicalStoppedChildPsi ring root s e + 1 ≤
        startPsi ring root s := by
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  obtain ⟨edge, hstrict⟩ := clockAbstractNominated n r w hn
  refine ⟨clockPhysicalEdgeOfAbstract ring root edge, ?_⟩
  have hEq := clockPhysicalStoppedChildTransport
    ring root s hn edge (hfixed _)
  have hh := clockAbstractChildStrict n r w edge hstrict
  calc
    clockPhysicalStoppedChildPsi ring root s
        (clockPhysicalEdgeOfAbstract ring root edge) + 1 =
      clockAbstractChildPsi n r w edge + 1 :=
        congrArg (fun t : Nat => t + 1) hEq
    _ ≤ clockAbstractPsi n r w := hh
    _ = startPsi ring root s :=
      (clockStartPsiNormalize ring root s).symm

end L3

namespace L3

set_option autoImplicit false

/-!
The stop event is a selected S1 serializer row or
failure of WFixedRoot in the actual phiW successor.
-/

/-- The selected root service is an actual S1 serializer row. -/
def clockSerializerSOneService {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) : Prop :=
  e = root ∧
    (serW (s root) (s (ring.rightNeighbor root))).row = "S1"

/-- An actual service would leave the fixed-root domain. -/
def clockSerializerLostRootService {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) : Prop :=
  ¬ WFixedRoot ring root (phiW ring s e)

/-- Both kinds of exit are events of the selected physical service. -/
def clockSerializerExitService {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) : Prop :=
  clockSerializerSOneService ring root s e ∨
    clockSerializerLostRootService ring root s e

/-- A source whose chosen edge exits has a zero-potential successor. -/
noncomputable def clockSerializerExitChildPsi {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) : Nat := by
  classical
  exact if clockSerializerExitService ring root s e then 0
    else startPsi ring root (phiW ring s e)

/-- Absorbing stop state, separate from the physical ProjW cut. -/
inductive ClockSerializerStopNode (n : Nat) (c : Compiled) where
  | active : (Fin n → ProjW c) → ClockSerializerStopNode n c
  | stopped : ClockSerializerStopNode n c

/-- An active service performs phiW once, then either exits or
    retains its real physical successor. -/
noncomputable def clockSerializerStoppedNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (x : ClockSerializerStopNode n c) (e : Fin n) :
    ClockSerializerStopNode n c := by
  classical
  cases x with
  | stopped =>
    exact .stopped
  | active s =>
    exact if clockSerializerExitService ring root s e then .stopped
      else .active (phiW ring s e)

/-- Terminal detection for the generic hitting-time interface. -/
def clockSerializerIsStopped {n : Nat} {c : Compiled} :
    ClockSerializerStopNode n c → Prop
  | .stopped => True
  | .active _ => False

/-- The stopped rank charges the real startPsi on active cuts. -/
def clockSerializerStoppedRank {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    ClockSerializerStopNode n c → Nat
  | .stopped => 0
  | .active s => startPsi ring root s

theorem clockSerializerStopOnExit {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (h : clockSerializerExitService ring root s e) :
    clockSerializerStoppedNext ring root (.active s) e =
      (.stopped : ClockSerializerStopNode n c) := by
  classical
  simp [clockSerializerStoppedNext, h]

theorem clockSerializerContinueOnSurvival {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (h : ¬ clockSerializerExitService ring root s e) :
    clockSerializerStoppedNext ring root (.active s) e =
      .active (phiW ring s e) := by
  classical
  simp [clockSerializerStoppedNext, h]

theorem clockSerializerStoppedAbsorbing {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (e : Fin n) :
    clockSerializerStoppedNext ring root
      (.stopped : ClockSerializerStopNode n c) e = .stopped := by
  rfl

/-- Exactly the old physical successor potential when no exit is
    taken; exactly zero on either exit. -/
theorem clockSerializerActiveChildRank {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) :
    clockSerializerStoppedRank ring root
      (clockSerializerStoppedNext ring root (.active s) e) =
        clockSerializerExitChildPsi ring root s e := by
  classical
  by_cases h : clockSerializerExitService ring root s e
  · simp [clockSerializerStoppedNext, clockSerializerStoppedRank,
      clockSerializerExitChildPsi, h]
  · simp [clockSerializerStoppedNext, clockSerializerStoppedRank,
      clockSerializerExitChildPsi, h]

/-- The exit event records the precise physical hitting boundary. -/
theorem clockSerializerStoppedNextIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) :
    clockSerializerIsStopped
      (clockSerializerStoppedNext ring root (.active s) e) ↔
      clockSerializerExitService ring root s e := by
  classical
  by_cases h : clockSerializerExitService ring root s e
  · simp [clockSerializerStoppedNext, clockSerializerIsStopped, h]
  · simp [clockSerializerStoppedNext, clockSerializerIsStopped, h]

/-- Every physical child is weak, because an unfixed successor is
    replaced by the zero-potential exit, rather than assumed away. -/
theorem clockSerializerExitChildWeak {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) (e : Fin n) :
    clockSerializerExitChildPsi ring root s e ≤
      startPsi ring root s := by
  classical
  by_cases hstop : clockSerializerExitService ring root s e
  · simp [clockSerializerExitChildPsi, hstop]
  · have hfixed : WFixedRoot ring root (phiW ring s e) := by
      by_cases h : WFixedRoot ring root (phiW ring s e)
      · exact h
      · exact False.elim
          (hstop (Or.inr (show
            clockSerializerLostRootService ring root s e from h)))
    have hnotSOne :
        e = root →
        (serW (s root) (s (ring.rightNeighbor root))).row ≠ "S1" := by
      intro he hs
      exact hstop (Or.inl ⟨he, hs⟩)
    have hweak :=
      clockPhiEveryNonterminalPsiWeak ring root s hn e hfixed
        hnotSOne
    simpa only [clockSerializerExitChildPsi, if_neg hstop]
      using hweak

/-- The abstract nominated edge remains strictly decreasing in
    the physical stopped kernel: failed-root successors go to zero. -/
theorem clockSerializerExitChildNominated {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) :
    ∃ e : Fin n,
      clockSerializerExitChildPsi ring root s e + 1 ≤
        startPsi ring root s := by
  classical
  let r := rootClass (s root).ser
  let w := clockPhysicalShapeWord ring root s
  obtain ⟨edge, hstrict⟩ := clockAbstractNominated n r w hn
  let e := clockPhysicalEdgeOfAbstract ring root edge
  have habs := clockAbstractChildStrict n r w edge hstrict
  have hparent : clockAbstractPsi n r w = startPsi ring root s :=
    (clockStartPsiNormalize ring root s).symm
  have hpositive : 1 ≤ startPsi ring root s := by
    rw [← hparent]
    omega
  refine ⟨e, ?_⟩
  by_cases hstop : clockSerializerExitService ring root s e
  · have hzero : clockSerializerExitChildPsi ring root s e = 0 := by
      simp [clockSerializerExitChildPsi, hstop]
    rw [hzero, Nat.zero_add]
    exact hpositive
  · have hfixed : WFixedRoot ring root (phiW ring s e) := by
      by_cases hf : WFixedRoot ring root (phiW ring s e)
      · exact hf
      · exact False.elim
          (hstop (Or.inr (show
            clockSerializerLostRootService ring root s e from hf)))
    have hnotSOne :
        ¬ (e = root ∧
          (serW (s root) (s (ring.rightNeighbor root))).row = "S1") := by
      intro h
      exact hstop (Or.inl h)
    have hvalue :
        clockSerializerExitChildPsi ring root s e =
          clockPhysicalStoppedChildPsi ring root s e := by
      unfold clockSerializerExitChildPsi clockPhysicalStoppedChildPsi
      rw [if_neg hstop, if_neg hnotSOne]
    have htransport := clockPhysicalStoppedChildTransport
      ring root s hn edge hfixed
    calc
      clockSerializerExitChildPsi ring root s e + 1 =
          clockPhysicalStoppedChildPsi ring root s e + 1 :=
        congrArg (fun t : Nat => t + 1) hvalue
      _ = clockAbstractChildPsi n r w edge + 1 :=
        congrArg (fun t : Nat => t + 1) htransport
      _ ≤ clockAbstractPsi n r w := habs
      _ = startPsi ring root s := hparent

/-- All physical services are weak, while at least one is strict;
    the nominated service is a true Fin n edge. -/
theorem clockSerializerStoppedLiveRows {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) :
    (∀ e : Fin n,
       clockSerializerStoppedRank ring root
         (clockSerializerStoppedNext ring root (.active s) e) ≤
       clockSerializerStoppedRank ring root (.active s)) ∧
    (∃ e : Fin n,
       clockSerializerStoppedRank ring root
         (clockSerializerStoppedNext ring root (.active s) e) + 1 ≤
       clockSerializerStoppedRank ring root (.active s)) := by
  constructor
  · intro e
    rw [clockSerializerActiveChildRank]
    exact clockSerializerExitChildWeak ring root s hn e
  · obtain ⟨e, hs⟩ :=
      clockSerializerExitChildNominated ring root s hn
    refine ⟨e, ?_⟩
    rw [clockSerializerActiveChildRank]
    exact hs

/-- The stopped potential has the same sharp initial cap. -/
theorem clockSerializerStoppedRankCap {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (x : ClockSerializerStopNode n c) :
    clockSerializerStoppedRank ring root x ≤ 5 * n - 4 := by
  cases x with
  | stopped =>
    exact Nat.zero_le _
  | active s =>
    exact clockStartPsiCap ring root s hn

/-- The closure obligation reserved for the headline: every service
    in a G-invariant state retains G and the same fixed physical root.
    It is a named proposition here, not a proved closure theorem. -/
def ClockSerializerNoRootLossFromG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop) : Prop :=
  (∀ s, G s → WFixedRoot ring root s) ∧
  (∀ s, G s → ∀ e, G (phiW ring s e) ∧
    WFixedRoot ring root (phiW ring s e))

/-- Under the named closure assertion, the lost-root exit is absent
    on every G service (including its S1 service). -/
theorem clockSerializerNoLostRootAtG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (s : Fin n → ProjW c) (hs : G s) (e : Fin n) :
    ¬ clockSerializerLostRootService ring root s e := by
  intro h
  exact h ((hG.2 s hs e).2)

/-- On G, the stopped exit agrees exactly with S1. -/
theorem clockSerializerStopEventAtG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (s : Fin n → ProjW c) (hs : G s) (e : Fin n) :
    clockSerializerExitService ring root s e ↔
      clockSerializerSOneService ring root s e := by
  constructor
  · intro h
    rcases h with hSOne | hLost
    · exact hSOne
    · exact False.elim
        ((clockSerializerNoLostRootAtG ring root G hG s hs e) hLost)
  · intro h
    exact Or.inl h


/-- A surviving physical edge retains WFixedRoot by the definition
    of the lost-root exit, with no closure theorem assumed. -/
theorem clockSerializerSurvivingRootFixed {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (h : ¬ clockSerializerExitService ring root s e) :
    WFixedRoot ring root (phiW ring s e) := by
  by_cases hf : WFixedRoot ring root (phiW ring s e)
  · exact hf
  · exact False.elim
      (h (Or.inr (show
        clockSerializerLostRootService ring root s e from hf)))

/-- A stopped node is admissible; active cuts are admissible when
    they retain the same fixed root. -/
def clockSerializerStoppedDomain {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    ClockSerializerStopNode n c → Prop
  | .stopped => True
  | .active s => WFixedRoot ring root s

/-- Every actual successor remains in the stopped-domain invariant;
    root loss goes to terminal instead of requiring WFixedRoot. -/
theorem clockSerializerStoppedDomainNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (x : ClockSerializerStopNode n c)
    (hx : clockSerializerStoppedDomain ring root x)
    (e : Fin n) :
    clockSerializerStoppedDomain ring root
      (clockSerializerStoppedNext ring root x e) := by
  classical
  cases x with
  | stopped =>
    simp [clockSerializerStoppedNext, clockSerializerStoppedDomain]
  | active s =>
    by_cases hstop : clockSerializerExitService ring root s e
    · simp [clockSerializerStoppedNext,
        clockSerializerStoppedDomain, hstop]
    · have hf := clockSerializerSurvivingRootFixed
        ring root s e hstop
      simpa [clockSerializerStoppedNext,
        clockSerializerStoppedDomain, hstop] using hf


/-- A uniform finite sum of values bounded by V is at most n V.
    This proof uses only core List.ofFn and Nat arithmetic. -/
private theorem clockFinSumWeak :
    ∀ (n : Nat) (f : Fin n → Nat) (V : Nat),
      (∀ e, f e ≤ V) →
      (List.ofFn f).sum ≤ n * V := by
  intro n
  induction n with
  | zero =>
    intro f V _
    simp
  | succ n ih =>
    intro f V hweak
    rw [List.ofFn_succ, List.sum_cons]
    have hz : f 0 ≤ V := hweak 0
    have ht := ih (fun e : Fin n => f e.succ) V
      (fun e => hweak e.succ)
    calc
      f 0 + (List.ofFn (fun e : Fin n => f e.succ)).sum ≤
          V + n * V := Nat.add_le_add hz ht
      _ = Nat.succ n * V := by
        rw [Nat.succ_mul]
        omega

/-- One nominated strict coordinate saves one ticket in the
    full n-edge Cartesian sum. No probabilistic API is needed. -/
private theorem clockFinSumStrict :
    ∀ (n : Nat) (f : Fin n → Nat) (chosen : Fin n) (V : Nat),
      (∀ e, f e ≤ V) →
      f chosen + 1 ≤ V →
      1 + (List.ofFn f).sum ≤ n * V := by
  intro n
  induction n with
  | zero =>
    intro f chosen V _ _
    exact Fin.elim0 chosen
  | succ n ih =>
    intro f chosen V hweak hstrict
    rw [List.ofFn_succ, List.sum_cons]
    cases chosen using Fin.cases with
    | zero =>
      have hz : f 0 + 1 ≤ V := hstrict
      have ht := clockFinSumWeak n
        (fun e : Fin n => f e.succ) V
        (fun e => hweak e.succ)
      calc
        1 + (f 0 + (List.ofFn
            (fun e : Fin n => f e.succ)).sum) =
          (f 0 + 1) + (List.ofFn
            (fun e : Fin n => f e.succ)).sum := by omega
        _ ≤ V + n * V := Nat.add_le_add hz ht
        _ = Nat.succ n * V := by
          rw [Nat.succ_mul]
          omega
    | succ i =>
      have hz : f 0 ≤ V := hweak 0
      have ht := ih (fun e : Fin n => f e.succ) i V
        (fun e => hweak e.succ) hstrict
      calc
        1 + (f 0 + (List.ofFn
            (fun e : Fin n => f e.succ)).sum) =
          f 0 + (1 + (List.ofFn
            (fun e : Fin n => f e.succ)).sum) := by omega
        _ ≤ V + n * V := Nat.add_le_add hz ht
        _ = Nat.succ n * V := by
          rw [Nat.succ_mul]
          omega

/-- Scaling every Fin coordinate by a constant commutes with sum. -/
private theorem clockFinSumMul :
    ∀ (n : Nat) (f : Fin n → Nat) (a : Nat),
      (List.ofFn (fun e : Fin n => a * f e)).sum =
        a * (List.ofFn f).sum := by
  intro n
  induction n with
  | zero =>
    intro f a
    simp
  | succ n ih =>
    intro f a
    have ht := ih (fun e : Fin n => f e.succ) a
    calc
      (List.ofFn (fun e : Fin (n + 1) => a * f e)).sum =
          a * f 0 + (List.ofFn
            (fun e : Fin n => a * f e.succ)).sum := by
              rw [List.ofFn_succ, List.sum_cons]
      _ = a * f 0 +
          a * (List.ofFn (fun e : Fin n => f e.succ)).sum := by
            rw [ht]
      _ = a * (List.ofFn f).sum := by
            rw [List.ofFn_succ, List.sum_cons, Nat.mul_add]

/-- One-unit drift in the real stopped kernel, summed over all
    n actual physical service edges. -/
theorem clockSerializerStoppedDrift {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) :
    1 + (List.ofFn (fun e : Fin n =>
      clockSerializerStoppedRank ring root
        (clockSerializerStoppedNext ring root (.active s) e))).sum ≤
    n * clockSerializerStoppedRank ring root (.active s) := by
  obtain ⟨hweak, ⟨chosen, hstrict⟩⟩ :=
    clockSerializerStoppedLiveRows ring root s hn
  exact clockFinSumStrict n
    (fun e : Fin n => clockSerializerStoppedRank ring root
      (clockSerializerStoppedNext ring root (.active s) e))
    chosen (clockSerializerStoppedRank ring root (.active s))
    hweak hstrict

/-- The exact n-scaled Bellman drift needed by the finite-horizon
    costNumerator API, without claiming an import-dependent theorem. -/
theorem clockSerializerStoppedScaledDrift {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n) :
    n + (List.ofFn (fun e : Fin n =>
      n * clockSerializerStoppedRank ring root
        (clockSerializerStoppedNext ring root (.active s) e))).sum ≤
    n * (n * clockSerializerStoppedRank ring root (.active s)) := by
  let f : Fin n → Nat := fun e =>
    clockSerializerStoppedRank ring root
      (clockSerializerStoppedNext ring root (.active s) e)
  let V := clockSerializerStoppedRank ring root (.active s)
  have hbase : 1 + (List.ofFn f).sum ≤ n * V :=
    clockSerializerStoppedDrift ring root s hn
  have hscaled := Nat.mul_le_mul_left n hbase
  calc
    n + (List.ofFn (fun e : Fin n => n * f e)).sum =
        n * (1 + (List.ofFn f).sum) := by
          rw [clockFinSumMul n f n, Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * V) := hscaled

/-- The same drift premise for every nonterminal abstract stop node.
    This is the precise API handoff to Prob.costNumerator_le_of_potential. -/
theorem clockSerializerStoppedNonterminalDrift {n : Nat}
    {c : Compiled} (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (x : ClockSerializerStopNode n c)
    (hnot : ¬ clockSerializerIsStopped x) :
    n + (List.ofFn (fun e : Fin n =>
      n * clockSerializerStoppedRank ring root
        (clockSerializerStoppedNext ring root x e))).sum ≤
    n * (n * clockSerializerStoppedRank ring root x) := by
  cases x with
  | stopped =>
    exact False.elim (hnot True.intro)
  | active s =>
    exact clockSerializerStoppedScaledDrift ring root s hn


/-- The literal physical S1 event is the REQUESTED-root row,
    on the successor-fixed branch where the table applies. -/
theorem clockSerializerSOneIffRequested {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 2 ≤ n)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (e : Fin n) :
    clockSerializerSOneService ring root s e ↔
      (e = root ∧ (s root).ser.cert = .REQUESTED) := by
  have hs := clockPhysicalSOneIff ring root s hn hfixed
  constructor
  · intro h
    change e = root ∧
      (serW (s root) (s (ring.rightNeighbor root))).row = "S1" at h
    exact ⟨h.1, hs.mp h.2⟩
  · intro h
    exact ⟨h.1, hs.mpr h.2⟩

end L3
