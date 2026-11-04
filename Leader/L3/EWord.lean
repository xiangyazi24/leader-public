import Leader.L3.Target

/-!
Validation layer.
Only local lemmas are stated; total transport is open.
-/

namespace L3
namespace EWord

set_option autoImplicit false

inductive ValidationStage
  | forward
  | returning
  deriving DecidableEq, Repr

/-- Proof-only state. `fresh` records a *real* zero-lease S1,
not a pattern match on the current serializer bytes. -/
structure ValidationGhost where
  fresh : Bool
  scrub : Nat
  stage : ValidationStage
  pivot : Nat
  deriving DecidableEq, Repr

def freshGhost : ValidationGhost :=
  { fresh := true, scrub := 2, stage := .forward, pivot := 0 }

def site {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (k : Nat) : Fin n :=
  PPL.shiftRight ring root k

def doneParent {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (i : Nat) : Prop :=
  (s (site ring root i)).ser.phase = .B ∧
  (s (site ring root i)).ser.out = .DONE ∧
  (s (site ring root i)).ser.wphase = .VALIDATING

/-- Only the current, causally challenged C child is admitted. -/
def pendingChild {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (a : Nat) : Prop :=
  (s (site ring root (a + 1))).ser.phase = .C ∧
  (((s (site ring root (a + 1))).ser.probe = .PENDING ∧
      (s (site ring root (a + 1))).ser.wphase = .VALIDATING) ∨
   (a + 2 < n ∧
      (s (site ring root (a + 1))).ser.probe = .INTERNAL_OK ∧
      (s (site ring root (a + 1))).ser.wphase = .VALIDATING) ∨
   (a + 2 = n ∧
      (s (site ring root (a + 1))).ser.probe = .LEAF_OK ∧
      (s (site ring root (a + 1))).ser.wphase = .OFF))

structure ForwardShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost) : Prop where
  isForward : g.stage = .forward
  pivotBound : g.pivot + 1 < n
  completed : ∀ i : Fin n, i.val < g.pivot →
    doneParent ring root s i.val
  parentB : (s (site ring root g.pivot)).ser.phase = .B
  parentValidating :
    (s (site ring root g.pivot)).ser.wphase = .VALIDATING
  currentObligation :
    (0 < g.pivot ∧
      (s (site ring root g.pivot)).ser.out = .NEW ∧
      g.scrub = g.pivot + 1) ∨
    ((s (site ring root g.pivot)).ser.out = .WAIT ∧
      g.scrub = g.pivot + 2 ∧
      pendingChild ring root s g.pivot)
  /-- Derived from the completed-link geometry; written explicitly
  because it is the actual root nonacceptance test during FORWARD. -/
  rootFront :
    (s root).ser.out = .WAIT ∨
    (s (ring.rightNeighbor root)).ser.phase = .B

structure ReturnShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost) : Prop where
  isReturn : g.stage = .returning
  covered : g.scrub = n
  pivotPositive : 0 < g.pivot
  pivotBound : g.pivot < n
  completed : ∀ i : Fin n, i.val < g.pivot →
    doneParent ring root s i.val
  leftmostF : (s (site ring root g.pivot)).ser.phase = .F
  leftmostWphase :
    (s (site ring root g.pivot)).ser.wphase =
      (if g.pivot + 1 = n then .OFF else .CURRENT)
  suffix : ∀ i : Fin n, g.pivot < i.val →
    (((s (site ring root i.val)).ser.phase = .F ∧
        (s (site ring root i.val)).ser.wphase =
          (if i.val + 1 = n then .OFF else .CURRENT)) ∨
     ((s (site ring root i.val)).ser.phase = .C ∧
        (s (site ring root i.val)).ser.wphase = .OFF))

/-- ValidationShape is a real serializer/worker assertion.
The covered prefix is EXACT offSI, because entry and extension
are actual hard S1/I1 overwrites; all unvisited suffix SI/serializer
fields are unconstrained. -/
structure ValidationShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost) : Prop where
  genuine : g.fresh = true
  protectedRoot : WFixedRoot ring root s
  width : 3 ≤ n
  rootRunning : (s root).ser.cert = .RUNNING
  rootValidating : (s root).ser.wphase = .VALIDATING
  lower : 2 ≤ g.scrub
  upper : g.scrub ≤ n
  scrubbed : ∀ i : Fin n, i.val < g.scrub →
    (s (site ring root i.val)).si = offSI c.t
  stageShape : ForwardShape ring root s g ∨ ReturnShape ring root s g

/-! Root hard S1 establishment, source lines 303, 321-325, 336-337. -/

theorem freshStartFlags {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED)
    (hz : x.siLease.val = 0) :
    (serW x y).row = "S1" ∧
    (serW x y).hard.hardS1 = true ∧
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.hardLeft = true ∧
    (serW x y).hard.hardRight = true := by
  simp [serW, serializerStep, ProjW.lift,
    serTbStar, hx, hy, hc, hz]

theorem freshStartSerializer {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED)
    (hz : x.siLease.val = 0) :
    (serW x y).x.phase = .B ∧
    (serW x y).x.out = .WAIT ∧
    (serW x y).x.cert = .RUNNING ∧
    (serW x y).x.wphase = .VALIDATING ∧
    (serW x y).y.phase = .C ∧
    (serW x y).y.probe = .PENDING ∧
    (serW x y).y.wphase = .VALIDATING := by
  simp [serW, serializerStep, ProjW.lift,
    serTbStar, hx, hy, hc, hz]

/-! Exact I1, composed-full.mjs:390-397. -/

theorem eraseRightLiteral (c : Compiled)
    (x y : Agent c) (post : PostE) (h : HardFlags)
    (ha : h.hardAccept = false)
    (hr : h.hardRight = true) :
    (siStep c x y post h).row = "I1" ∧
    (siStep c x y post h).y = offSI c.t := by
  simp [siStep, ha, hr]

theorem eraseLeftLiteral (c : Compiled)
    (x y : Agent c) (post : PostE) (h : HardFlags)
    (ha : h.hardAccept = false)
    (hl : h.hardLeft = true) :
    (siStep c x y post h).row = "I1" ∧
    (siStep c x y post h).x = offSI c.t := by
  simp [siStep, ha, hl]

theorem freshStartWorker {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED)
    (hz : x.siLease.val = 0) :
    (workerW x y).row = "I1" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = offSI c.t := by
  have h := freshStartFlags x y hx hy hc hz
  have ha := h.2.2.1
  have hl := h.2.2.2.1
  have hr := h.2.2.2.2
  simp [workerW, siStep, ha, hl, hr]

theorem pairOwnerFields {c : Compiled} (x y : ProjW c) :
    (pairW x y).1.ser = (serW x y).x ∧
    (pairW x y).2.ser = (serW x y).y ∧
    (pairW x y).1.si = (workerW x y).x ∧
    (pairW x y).2.si = (workerW x y).y := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Arbitrary selected OLD fields establish the two initial
physical/serializer records; all remote sites frame. -/
theorem freshStartPair {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .REQUESTED)
    (hz : x.siLease.val = 0) :
    (pairW x y).1.si = offSI c.t ∧
    (pairW x y).2.si = offSI c.t ∧
    (pairW x y).1.ser.phase = .B ∧
    (pairW x y).1.ser.out = .WAIT ∧
    (pairW x y).1.ser.cert = .RUNNING ∧
    (pairW x y).1.ser.wphase = .VALIDATING ∧
    (pairW x y).2.ser.phase = .C ∧
    (pairW x y).2.ser.probe = .PENDING ∧
    (pairW x y).2.ser.wphase = .VALIDATING := by
  have hw := freshStartWorker x y hx hy hc hz
  have hs := freshStartSerializer x y hx hy hc hz
  change
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = offSI c.t ∧
    (serW x y).x.phase = .B ∧
    (serW x y).x.out = .WAIT ∧
    (serW x y).x.cert = .RUNNING ∧
    (serW x y).x.wphase = .VALIDATING ∧
    (serW x y).y.phase = .C ∧
    (serW x y).y.probe = .PENDING ∧
    (serW x y).y.wphase = .VALIDATING
  exact ⟨hw.2.1, hw.2.2, hs⟩

/-! The two critical physical scrub theorems. -/

theorem validatingHardLeft {c : Compiled} (x y : ProjW c)
    (hv : x.ser.wphase = .VALIDATING) :
    (serW x y).hard.hardLeft = true := by
  simp [serW, serializerStep, ProjW.lift, hv]

theorem nonrootNoAccept {c : Compiled} (x y : ProjW c)
    (hn : (postW x y).eX.l = false) :
    (serW x y).hard.hardAccept = false := by
  simp [serW, serializerStep, ProjW.lift, hn]

theorem waitNoAccept {c : Compiled} (x y : ProjW c)
    (hw : x.ser.out = .WAIT) :
    (serW x y).hard.hardAccept = false := by
  simp [serW, serializerStep, ProjW.lift, hw]

theorem childBNoAccept {c : Compiled} (x y : ProjW c)
    (hb : y.ser.phase = .B) :
    (serW x y).hard.hardAccept = false := by
  simp [serW, serializerStep, ProjW.lift, hb]

/-- Any VALIDATING frontier forces I1 before all ordinary worker
rows when no hardAccept is selected. -/
theorem frontierLeftBarrier {c : Compiled} (x y : ProjW c)
    (hv : x.ser.wphase = .VALIDATING)
    (ha : (serW x y).hard.hardAccept = false) :
    (serW x y).hard.hardLeft = true ∧
    (workerW x y).row = "I1" ∧
    (workerW x y).x = offSI c.t := by
  have hl := validatingHardLeft x y hv
  have hs := eraseLeftLiteral c x.lift y.lift
    (postW x y) (serW x y).hard ha hl
  exact ⟨hl, hs.1, hs.2⟩

/-- A VALIDATING B/NEW challenges regardless of the current
responder phase C/B/F. Thus hardRight clears a new child. -/
theorem freshChildGuards {c : Compiled} (x y : ProjW c)
    (hp : x.ser.phase = .B)
    (hn : x.ser.out = .NEW)
    (hv : x.ser.wphase = .VALIDATING) :
    (serW x y).hard.hardChallenge = true ∧
    (serW x y).hard.hardRight = true ∧
    (serW x y).hard.hardLeft = true ∧
    (serW x y).hard.hardAccept = false := by
  cases hy : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, hp, hn, hv, hy]

theorem freshChildRightScrub {c : Compiled} (x y : ProjW c)
    (hp : x.ser.phase = .B)
    (hn : x.ser.out = .NEW)
    (hv : x.ser.wphase = .VALIDATING) :
    (serW x y).hard.hardRight = true ∧
    (workerW x y).row = "I1" ∧
    (workerW x y).y = offSI c.t := by
  have hf := freshChildGuards x y hp hn hv
  have hs := eraseRightLiteral c x.lift y.lift
    (postW x y) (serW x y).hard hf.2.2.2 hf.2.1
  exact ⟨hf.2.1, hs.1, hs.2⟩

theorem validatingRightAtSeam {c : Compiled} (x y : ProjW c)
    (hv : y.ser.wphase = .VALIDATING) :
    (serW x y).hard.hardRight = true := by
  simp [serW, serializerStep, ProjW.lift, hv]

theorem rootSeamBarrier {c : Compiled} (x y : ProjW c)
    (hv : y.ser.wphase = .VALIDATING)
    (hn : (postW x y).eX.l = false) :
    (workerW x y).row = "I1" ∧
    (workerW x y).y = offSI c.t := by
  have ha := nonrootNoAccept x y hn
  have hr := validatingRightAtSeam x y hv
  exact eraseRightLiteral c x.lift y.lift
    (postW x y) (serW x y).hard ha hr

/-! Transport lemmas that do not require global ghost updates. -/

theorem remoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e i : Fin n) (he : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    (phiW ring s e) i = s i := by
  simp [phiW, projectedEdge, he, hj]

theorem cleanRemoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e i : Fin n) (he : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e)
    (h : (s i).si = offSI c.t) :
    ((phiW ring s e) i).si = offSI c.t := by
  rw [remoteFrame ring s e i he hj]
  exact h

theorem twoFreeLiteral (c : Compiled)
    (x y : Agent c) (post : PostE) (h : HardFlags)
    (ha : h.hardAccept = false)
    (hx : x.si = offSI c.t) (hy : y.si = offSI c.t) :
    (siStep c x y post h).x = offSI c.t ∧
    (siStep c x y post h).y = offSI c.t := by
  cases hl : h.hardLeft <;>
  cases hr : h.hardRight <;>
    simp [siStep, ha, hx, hy, hl, hr, freeSI, offSI]

theorem twoFreeSelected {c : Compiled} (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = false)
    (hx : x.si = offSI c.t) (hy : y.si = offSI c.t) :
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = offSI c.t := by
  exact twoFreeLiteral c x.lift y.lift
    (postW x y) (serW x y).hard ha hx hy

/-! The clean-acceptance implication is separate from global closure. -/

theorem forwardNoAccept {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g) :
    (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = false := by
  rcases hf.rootFront with hw | hb
  · exact waitNoAccept (s root) (s (ring.rightNeighbor root)) hw
  · exact childBNoAccept (s root) (s (ring.rightNeighbor root)) hb

/-- If a physical root hardAccept happens inside the shape, it
cannot be FORWARD. RETURN has scrub=n and all sites are offSI.
In particular all nonroot SI records are free before I0. -/
theorem hardAcceptInsideShapeIsClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (h : ValidationShape ring root s g)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ∀ i : Fin n, 0 < i.val →
      freeSI (s (site ring root i.val)).si = true := by
  have hr : ReturnShape ring root s g := by
    rcases h.stageShape with hf | hr
    · have hfalse := forwardNoAccept ring root s g hf
      rw [hfalse] at ha
      cases ha
    · exact hr
  intro i _
  have hi : (s (site ring root i.val)).si = offSI c.t :=
    h.scrubbed i (by
      rw [hr.covered]
      exact i.isLt)
  rw [hi]
  rfl

/-!
OPEN: actual root WFixedRoot/Protected native-E preservation;
whole-ring ValidationShape establishment from the S1 pair certificate;
full four-edge-class inductive shape preservation (S0-S7, SI, E);
epoch composition preventing a second I0 with old SI;
first A0/QWord bridge and its expected-time bound.
Do not use the clean-acceptance implication as a substitute for
inductively establishing ValidationShape on actual execution traces.
-/

end EWord
end L3

/-!
The results below separate the terminal accepting edge from the
nonaccepting validation transport.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! Geometry of the directed-ring indexing used by the ghost. -/

theorem siteZero {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : site ring root 0 = root := by
  apply Fin.ext
  simp [site, PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

theorem siteOne {n : Nat} (ring : DirectedRing n)
    (root : Fin n) :
    site ring root 1 = ring.rightNeighbor root := rfl

theorem siteAdd {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (a b : Nat) :
    site ring (site ring root a) b = site ring root (a + b) := by
  apply Fin.ext
  change (((root.val + a) % n + b) % n) =
    (root.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem siteSuccessor {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (k : Nat) :
    ring.rightNeighbor (site ring root k) =
      site ring root (k + 1) := by
  change site ring (site ring root k) 1 =
    site ring root (k + 1)
  exact siteAdd ring root k 1

theorem rightNeighborDifferent {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (e : Fin n) :
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

theorem phiSource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) :
    (phiW ring s e) e =
      (pairW (s e) (s (ring.rightNeighbor e))).1 := by
  simp only [phiW, projectedEdge, if_pos rfl]

theorem phiResponder {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    (phiW ring s e) (ring.rightNeighbor e) =
      (pairW (s e) (s (ring.rightNeighbor e))).2 := by
  simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]

/-! (A) Complete whole-ring fresh S1 establishment, conditional
only on the specified native-layer WFixedRoot AFTER the edge.
All inherited serializer, SI, u, beta, and lease fields except the
selected root's old REQUESTED/zero-lease facts are arbitrary. -/

theorem freshStartWholeRing {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hn : 3 ≤ n)
    (hx : (postW (s root)
      (s (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (s root)
      (s (ring.rightNeighbor root))).eY.l = false)
    (hc : (s root).ser.cert = .REQUESTED)
    (hz : (s root).siLease.val = 0)
    (hfixed : WFixedRoot ring root (phiW ring s root)) :
    ValidationShape ring root (phiW ring s root) freshGhost := by
  have hne : ring.rightNeighbor root ≠ root :=
    rightNeighborDifferent ring (by omega) root
  have hsrc := phiSource ring s root
  have hdst := phiResponder ring s root hne
  obtain ⟨hsiX, hsiY, hBx, hwait, hrun, hval,
      hCy, hpend, hvalY⟩ :=
    freshStartPair (s root) (s (ring.rightNeighbor root))
      hx hy hc hz
  have hrootRun :
      ((phiW ring s root) root).ser.cert = .RUNNING := by
    rw [hsrc]
    exact hrun
  have hrootVal :
      ((phiW ring s root) root).ser.wphase = .VALIDATING := by
    rw [hsrc]
    exact hval
  have hchild :
      pendingChild ring root (phiW ring s root) 0 := by
    unfold pendingChild
    simp only [Nat.zero_add, siteOne, hdst]
    exact ⟨hCy, Or.inl ⟨hpend, hvalY⟩⟩
  have hforward :
      ForwardShape ring root (phiW ring s root) freshGhost := by
    refine {
      isForward := rfl
      pivotBound := ?_
      completed := ?_
      parentB := ?_
      parentValidating := ?_
      currentObligation := ?_
      rootFront := ?_ }
    · change 1 < n
      omega
    · intro i hi
      have hz0 : i.val < 0 := by
        simpa [freshGhost] using hi
      exact False.elim (Nat.not_lt_zero i.val hz0)
    · simpa [freshGhost, siteZero, hsrc] using hBx
    · simpa [freshGhost, siteZero, hsrc] using hval
    · right
      refine ⟨?_, ?_, hchild⟩
      · simpa [freshGhost, siteZero, hsrc] using hwait
      · rfl
    · exact Or.inl (by simpa [hsrc] using hwait)
  refine {
    genuine := rfl
    protectedRoot := hfixed
    width := hn
    rootRunning := hrootRun
    rootValidating := hrootVal
    lower := by decide
    upper := by change 2 ≤ n; omega
    scrubbed := ?_
    stageShape := Or.inl hforward }
  intro i hi
  have hsmall : i.val < 2 := by
    simpa [freshGhost] using hi
  have hcases : i.val = 0 ∨ i.val = 1 := by omega
  rcases hcases with hzero | hone
  · simpa [hzero, siteZero, hsrc] using hsiX
  · simpa [hone, siteOne, hdst] using hsiY

/-! (B) A ghost update reads only OLD S, g, e. Its accepted
result is TERMINAL: it is not a ValidationShape after I0. -/

def validationGhostStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n) : ValidationGhost :=
  let j := ring.rightNeighbor e
  let x := s e
  let y := s j
  let sr := serW x y
  if e == root && sr.hard.hardS1 then
    freshGhost
  else if g.stage == .forward then
    if e == site ring root g.pivot && x.ser.phase == .B then
      if x.ser.out == .NEW && x.ser.wphase == .VALIDATING &&
           sr.hard.hardChallenge then
        { g with scrub := g.scrub + 1 }
      else if x.ser.out == .WAIT && y.ser.phase == .C &&
           y.ser.probe == .INTERNAL_OK then
        { g with pivot := g.pivot + 1 }
      else if x.ser.out == .WAIT && y.ser.phase == .C &&
           y.ser.probe == .LEAF_OK then
        { g with stage := .returning, pivot := g.pivot + 1 }
      else g
    else g
  else if g.stage == .returning && 1 < g.pivot &&
       e == site ring root (g.pivot - 1) &&
       x.ser.phase == .B && x.ser.out == .DONE &&
       y.ser.phase == .F && sr.row == "S2N" then
    { g with pivot := g.pivot - 1 }
  else g

theorem ghostStepFresh {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hstart : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardS1 = true) :
    validationGhostStep ring root s g root = freshGhost := by
  simp [validationGhostStep, hstart]

/-! Physical edge-class certificates, lifted through actual phiW. -/

theorem coveredPairStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hx : (s e).si = offSI c.t)
    (hy : (s (ring.rightNeighbor e)).si = offSI c.t)
    (ha : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false) :
    ((phiW ring s e) e).si = offSI c.t ∧
    ((phiW ring s e) (ring.rightNeighbor e)).si =
      offSI c.t := by
  have h := twoFreeSelected (s e) (s (ring.rightNeighbor e))
    ha hx hy
  constructor
  · rw [phiSource]; exact h.1
  · rw [phiResponder ring s e hne]; exact h.2

theorem frontierLeftStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n)
    (hv : (s e).ser.wphase = .VALIDATING)
    (ha : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false) :
    ((phiW ring s e) e).si = offSI c.t := by
  have h := frontierLeftBarrier
    (s e) (s (ring.rightNeighbor e)) hv ha
  rw [phiSource]; exact h.2.2

theorem frontierChallengeStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hp : (s e).ser.phase = .B)
    (hn : (s e).ser.out = .NEW)
    (hv : (s e).ser.wphase = .VALIDATING) :
    ((phiW ring s e) e).si = offSI c.t ∧
    ((phiW ring s e) (ring.rightNeighbor e)).si =
      offSI c.t := by
  have hr := freshChildRightScrub
    (s e) (s (ring.rightNeighbor e)) hp hn hv
  have hf := freshChildGuards
    (s e) (s (ring.rightNeighbor e)) hp hn hv
  have hl := frontierLeftBarrier
    (s e) (s (ring.rightNeighbor e)) hv hf.2.2.2
  constructor
  · rw [phiSource]; exact hl.2.2
  · rw [phiResponder ring s e hne]; exact hr.2.2

theorem rootSeamStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hv : (s (ring.rightNeighbor e)).ser.wphase =
      .VALIDATING)
    (hn : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false) :
    ((phiW ring s e) (ring.rightNeighbor e)).si =
      offSI c.t := by
  have h := rootSeamBarrier
    (s e) (s (ring.rightNeighbor e)) hv hn
  rw [phiResponder ring s e hne]; exact h.2

theorem unvisitedRemoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (s : Fin n → ProjW c)
    (e i : Fin n)
    (he : i ≠ e)
    (hy : i ≠ ring.rightNeighbor e) :
    (phiW ring s e) i = s i :=
  remoteFrame ring s e i he hy

/-! A necessary TERMINAL case in the induction.
composed-full.mjs:305-306,340-341 selects S6 on a genuine
returned root. The serializer cert becomes IDLE; worker I0 starts
PREFIX(0). Hence ValidationShape itself is not closed over I0. -/

theorem acceptingSerializerTerminal {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .RUNNING)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hv : x.ser.wphase = .VALIDATING)
    (hf : y.ser.phase = .F) :
    (serW x y).row = "S6" ∧
    (serW x y).hard.hardAccept = true ∧
    (serW x y).x.cert = .IDLE ∧
    (serW x y).x.wphase = .CURRENT := by
  simp [serW, serializerStep, ProjW.lift, hx, hy,
    hc, hp, ho, hv, hf]

theorem acceptingPairRootIdle {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.cert = .RUNNING)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hv : x.ser.wphase = .VALIDATING)
    (hf : y.ser.phase = .F) :
    (pairW x y).1.ser.cert = .IDLE := by
  have h := acceptingSerializerTerminal x y
    hx hy hc hp ho hv hf
  change (serW x y).x.cert = .IDLE
  exact h.2.2.1

theorem terminalCannotPreserveShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hx : (postW (s root)
      (s (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (s root)
      (s (ring.rightNeighbor root))).eY.l = false)
    (hc : (s root).ser.cert = .RUNNING)
    (hp : (s root).ser.phase = .B)
    (ho : (s root).ser.out = .DONE)
    (hv : (s root).ser.wphase = .VALIDATING)
    (hf : (s (ring.rightNeighbor root)).ser.phase = .F) :
    ∀ g' : ValidationGhost,
      ¬ ValidationShape ring root (phiW ring s root) g' := by
  have hidle : ((phiW ring s root) root).ser.cert = .IDLE := by
    rw [phiSource]
    exact acceptingPairRootIdle (s root)
      (s (ring.rightNeighbor root)) hx hy hc hp ho hv hf
  intro g' hshape
  have hrun := hshape.rootRunning
  rw [hidle] at hrun
  cases hrun

/-! (C) Genuine-start trace, stopped before an actual I0.
The one-step inductive kernel remains an explicit, named missing
hypothesis; no unconditional closure theorem is manufactured. -/

inductive WValidationHistory {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    (Fin n → ProjW c) → ValidationGhost → Prop where
  | start (s : Fin n → ProjW c)
      (hn : 3 ≤ n)
      (hx : (postW (s root)
        (s (ring.rightNeighbor root))).eX.l = true)
      (hy : (postW (s root)
        (s (ring.rightNeighbor root))).eY.l = false)
      (hc : (s root).ser.cert = .REQUESTED)
      (hz : (s root).siLease.val = 0)
      (hfixed : WFixedRoot ring root (phiW ring s root)) :
      WValidationHistory ring root (phiW ring s root) freshGhost
  | next {s : Fin n → ProjW c} {g : ValidationGhost}
      (history : WValidationHistory ring root s g)
      (e : Fin n)
      (hno : (serW (s e)
        (s (ring.rightNeighbor e))).hard.hardAccept = false)
      (hfixed : WFixedRoot ring root (phiW ring s e)) :
      WValidationHistory ring root (phiW ring s e)
        (validationGhostStep ring root s g e)

/-- Exactly the missing nonaccepting all-edge lemma, separated
from the already proved endpoint certificates and from I0 exit. -/
def ValidationTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (s : Fin n → ProjW c) (g : ValidationGhost) (e : Fin n),
    ValidationShape ring root s g →
    WFixedRoot ring root (phiW ring s e) →
    (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false →
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e)

theorem validationHistorySound {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (htransport : ValidationTransport (c := c) ring root)
    {s : Fin n → ProjW c} {g : ValidationGhost}
    (history : WValidationHistory ring root s g) :
    ValidationShape ring root s g := by
  induction history with
  | start s hn hx hy hc hz hfixed =>
      exact freshStartWholeRing ring root s hn hx hy hc hz
        hfixed
  | next history e hno hfixed ih =>
      exact htransport _ _ _ ih hfixed hno

theorem validationHistoryHardAcceptClean
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (htransport : ValidationTransport (c := c) ring root)
    {s : Fin n → ProjW c} {g : ValidationGhost}
    (history : WValidationHistory ring root s g)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ∀ i : Fin n, 0 < i.val →
      freeSI (s (site ring root i.val)).si = true :=
  hardAcceptInsideShapeIsClean ring root s g
    (validationHistorySound ring root htransport history) ha

end EWord
end L3

/-!
The nonaccepting all-edge ValidationTransport is not
asserted.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! Priority classification of each physical edge.
The suffix case is *defined* by genuine remoteness from every
causally scrubbed site, so its proof does not assume geometry. -/

inductive ValidationEdgeClass
  | rootSeam
  | frontierParent
  | challengedChild
  | unvisitedSuffix
  | coveredInside
  deriving DecidableEq, Repr

def validationEdgeClass {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (g : ValidationGhost) (e : Fin n) :
    ValidationEdgeClass :=
  if e = site ring root (n - 1) then .rootSeam
  else if g.stage = .forward ∧ e = site ring root g.pivot then
    .frontierParent
  else if g.stage = .forward ∧
      e = site ring root (g.pivot + 1) then
    .challengedChild
  else if (∀ i : Fin n, i.val < g.scrub →
      site ring root i.val ≠ e ∧
      site ring root i.val ≠ ring.rightNeighbor e) then
    .unvisitedSuffix
  else .coveredInside

theorem validationEdgeClassCover {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (g : ValidationGhost) (e : Fin n) :
    validationEdgeClass ring root g e = .rootSeam ∨
    validationEdgeClass ring root g e = .frontierParent ∨
    validationEdgeClass ring root g e = .challengedChild ∨
    validationEdgeClass ring root g e = .unvisitedSuffix ∨
    validationEdgeClass ring root g e = .coveredInside := by
  cases h : validationEdgeClass ring root g e <;> simp [h]

/-- Unlike a mere guessed offset, this proves that a suffix-class
edge cannot touch either endpoint of an already covered site. -/
theorem unvisitedSuffixRemote {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (g : ValidationGhost) (e : Fin n)
    (hc : validationEdgeClass ring root g e =
      .unvisitedSuffix) :
    ∀ i : Fin n, i.val < g.scrub →
      site ring root i.val ≠ e ∧
      site ring root i.val ≠ ring.rightNeighbor e := by
  unfold validationEdgeClass at hc
  by_cases hs : e = site ring root (n - 1)
  · rw [if_pos hs] at hc
    cases hc
  · rw [if_neg hs] at hc
    by_cases hp : g.stage = .forward ∧
        e = site ring root g.pivot
    · rw [if_pos hp] at hc
      cases hc
    · rw [if_neg hp] at hc
      by_cases hy : g.stage = .forward ∧
          e = site ring root (g.pivot + 1)
      · rw [if_pos hy] at hc
        cases hc
      · rw [if_neg hy] at hc
        by_cases hr : ∀ i : Fin n, i.val < g.scrub →
            site ring root i.val ≠ e ∧
            site ring root i.val ≠ ring.rightNeighbor e
        · exact hr
        · rw [if_neg hr] at hc
          cases hc

/-! The general *color+SI* frame theorem. Native E, lease,
and visible word coordinates may change; the phase grammar
uses only covered serializer colors and SI plus WFixedRoot. -/

theorem coveredOffsetBound {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (shape : ValidationShape ring root s g)
    (k : Nat) (hk : k < g.scrub) : k < n :=
  Nat.lt_of_lt_of_le hk shape.upper

theorem validationCoveredSerSIFrame
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hser : ∀ i : Fin n, i.val < g.scrub →
      ((phiW ring s e) (site ring root i.val)).ser =
        (s (site ring root i.val)).ser)
    (hsi : ∀ i : Fin n, i.val < g.scrub →
      ((phiW ring s e) (site ring root i.val)).si =
        (s (site ring root i.val)).si) :
    ValidationShape ring root (phiW ring s e) g := by
  have hsNat : ∀ k : Nat, k < g.scrub →
      ((phiW ring s e) (site ring root k)).ser =
        (s (site ring root k)).ser := by
    intro k hk
    exact hser ⟨k, coveredOffsetBound ring root s g shape k hk⟩ hk
  have hroot : ((phiW ring s e) root).ser =
      (s root).ser := by
    simpa only [siteZero] using hsNat 0 (by have := shape.lower; have := shape.width; omega)
  have hfirst :
      ((phiW ring s e) (ring.rightNeighbor root)).ser =
        (s (ring.rightNeighbor root)).ser := by
    simpa only [siteOne] using hsNat 1 (by have := shape.lower; have := shape.width; omega)
  have hstage :
      ForwardShape ring root (phiW ring s e) g ∨
      ReturnShape ring root (phiW ring s e) g := by
    rcases shape.stageShape with hf | hr
    · have hpivot : g.pivot < g.scrub := by
        rcases hf.currentObligation with
          ⟨_, _, hk⟩ | ⟨_, hk, _⟩ <;> omega
      left
      refine {
        isForward := hf.isForward
        pivotBound := hf.pivotBound
        completed := ?_
        parentB := ?_
        parentValidating := ?_
        currentObligation := ?_
        rootFront := ?_ }
      · intro i hi
        have hc : i.val < g.scrub := Nat.lt_trans hi hpivot
        simpa only [doneParent, hsNat i.val hc] using
          hf.completed i hi
      · rw [hsNat g.pivot hpivot]
        exact hf.parentB
      · rw [hsNat g.pivot hpivot]
        exact hf.parentValidating
      · rcases hf.currentObligation with hn | hw
        · left
          refine ⟨hn.1, ?_, hn.2.2⟩
          rw [hsNat g.pivot hpivot]
          exact hn.2.1
        · right
          refine ⟨?_, hw.2.1, ?_⟩
          · rw [hsNat g.pivot hpivot]
            exact hw.1
          · have hchild : g.pivot + 1 < g.scrub := by
              have hk : g.scrub = g.pivot + 2 := hw.2.1
              omega
            simpa only [pendingChild,
              hsNat (g.pivot + 1) hchild] using hw.2.2
      · rcases hf.rootFront with hw | hb
        · left
          rw [hroot]
          exact hw
        · right
          rw [hfirst]
          exact hb
    · right
      have hpivot : g.pivot < g.scrub := by
        rw [hr.covered]
        exact hr.pivotBound
      refine {
        isReturn := hr.isReturn
        covered := hr.covered
        pivotPositive := hr.pivotPositive
        pivotBound := hr.pivotBound
        completed := ?_
        leftmostF := ?_
        leftmostWphase := ?_
        suffix := ?_ }
      · intro i hi
        have hc : i.val < g.scrub :=
          Nat.lt_trans hi hpivot
        simpa only [doneParent, hsNat i.val hc] using
          hr.completed i hi
      · rw [hsNat g.pivot hpivot]
        exact hr.leftmostF
      · rw [hsNat g.pivot hpivot]
        exact hr.leftmostWphase
      · intro i hi
        have hc : i.val < g.scrub := by
          rw [hr.covered]
          exact i.isLt
        simpa only [hsNat i.val hc] using hr.suffix i hi
  refine {
    genuine := shape.genuine
    protectedRoot := hfixed
    width := shape.width
    rootRunning := ?_
    rootValidating := ?_
    lower := shape.lower
    upper := shape.upper
    scrubbed := ?_
    stageShape := hstage }
  · rw [hroot]
    exact shape.rootRunning
  · rw [hroot]
    exact shape.rootValidating
  · intro i hi
    rw [hsi i hi]
    exact shape.scrubbed i hi

/-! A genuinely unvisited suffix neither changes the covered colors
nor imports inherited SI. Its ghost update is also stationary. -/

theorem unvisitedSuffixGhostUnchanged
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hremote : ∀ i : Fin n, i.val < g.scrub →
      site ring root i.val ≠ e ∧
      site ring root i.val ≠ ring.rightNeighbor e) :
    validationGhostStep ring root s g e = g := by
  have hremoteNat : ∀ k : Nat, k < g.scrub →
      site ring root k ≠ e := by
    intro k hk
    have hkN : k < n :=
      coveredOffsetBound ring root s g shape k hk
    exact (hremote ⟨k, hkN⟩ hk).1
  have hnotroot : e ≠ root := by
    intro he
    have hne := hremoteNat 0 (by have := shape.lower; have := shape.width; omega)
    apply hne
    rw [siteZero]
    exact he.symm
  rcases shape.stageShape with hf | hr
  · have hpivot : g.pivot < g.scrub := by
      rcases hf.currentObligation with
        ⟨_, _, hk⟩ | ⟨_, hk, _⟩ <;> omega
    have hnotparent :
        e ≠ site ring root g.pivot := by
      intro he
      exact hremoteNat g.pivot hpivot he.symm
    simp [validationGhostStep, hnotroot,
      hf.isForward, hnotparent]
  · by_cases hp : 1 < g.pivot
    · have hprev : g.pivot - 1 < g.scrub := by
        have hbound : g.pivot < n := hr.pivotBound
        rw [hr.covered]
        omega
      have hnotprev :
          e ≠ site ring root (g.pivot - 1) := by
        intro he
        exact hremoteNat (g.pivot - 1) hprev he.symm
      simp [validationGhostStep, hnotroot,
        hr.isReturn, hp, hnotprev]
    · simp [validationGhostStep, hnotroot,
        hr.isReturn, hp]

theorem validationUnvisitedSuffixClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (_hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hc : validationEdgeClass ring root g e =
      .unvisitedSuffix) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hr := unvisitedSuffixRemote ring root g e hc
  have hg := unvisitedSuffixGhostUnchanged
    ring root s g e shape hr
  rw [hg]
  apply validationCoveredSerSIFrame
    ring root s g e shape hfixed
  · intro i hi
    have hn := hr i hi
    rw [remoteFrame ring s e
      (site ring root i.val) hn.1 hn.2]
  · intro i hi
    have hn := hr i hi
    rw [remoteFrame ring s e
      (site ring root i.val) hn.1 hn.2]

/-! The inside-covered *idle* subrow is another complete class.
Only OLD serializer-field equalities and both canonical SI records
are required, not the desired post ValidationShape itself. -/

structure CoveredIdleClass {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n) : Prop where
  oldSourceOff : (s e).si = offSI c.t
  oldTargetOff : (s (ring.rightNeighbor e)).si =
    offSI c.t
  serializerX : (serW (s e)
    (s (ring.rightNeighbor e))).x = (s e).ser
  serializerY : (serW (s e)
    (s (ring.rightNeighbor e))).y =
      (s (ring.rightNeighbor e)).ser
  ghostFixed : validationGhostStep ring root s g e = g

theorem validationCoveredIdleClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hc : CoveredIdleClass ring root s g e) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by have := shape.lower; have := shape.width; omega) e
  have hsi := coveredPairStep ring s e hne
    hc.oldSourceOff hc.oldTargetOff hno
  rw [hc.ghostFixed]
  apply validationCoveredSerSIFrame
    ring root s g e shape hfixed
  · intro i hi
    by_cases he : site ring root i.val = e
    · rw [he, phiSource]
      exact hc.serializerX
    · by_cases hy :
          site ring root i.val = ring.rightNeighbor e
      · rw [hy, phiResponder ring s e hne]
        exact hc.serializerY
      · rw [remoteFrame ring s e
          (site ring root i.val) he hy]
  · intro i hi
    by_cases he : site ring root i.val = e
    · rw [he]
      exact hsi.1.trans hc.oldSourceOff.symm
    · by_cases hy :
          site ring root i.val = ring.rightNeighbor e
      · rw [hy]
        exact hsi.2.trans hc.oldTargetOff.symm
      · rw [remoteFrame ring s e
          (site ring root i.val) he hy]

/-- S2N internal B/DONE→B is an actual idle serializer subrow,
not an asserted word-control identity. -/
theorem internalDoneDoneSerFrame {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hp : x.ser.phase = .B)
    (ho : x.ser.out = .DONE)
    (hq : y.ser.phase = .B) :
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hp, ho, hq]

/-- A genuinely internal B/DONE→B row does not move the ghost:
it cannot be the current FORWARD parent (NEW or WAIT), and
on RETURN its responder is not F. -/
theorem internalDoneDoneGhostFixed {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (ho : (s e).ser.out = .DONE)
    (hy : (s (ring.rightNeighbor e)).ser.phase = .B) :
    validationGhostStep ring root s g e = g := by
  cases hstage : g.stage with
  | forward =>
      simp [validationGhostStep, hs, hstage, ho]
  | returning =>
      simp [validationGhostStep, hs, hstage, hy]

theorem nonrootHardStartFalse {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false) :
    (serW x y).hard.hardS1 = false := by
  simp [serW, serializerStep, ProjW.lift, hx]

/-- Complete full-shape theorem for the concrete S2N
B/DONE→B idle subrow when both selected SI are covered/free. -/
theorem validationInternalDoneDoneClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = false)
    (hp : (s e).ser.phase = .B)
    (ho : (s e).ser.out = .DONE)
    (hq : (s (ring.rightNeighbor e)).ser.phase = .B)
    (hsix : (s e).si = offSI c.t)
    (hsiy : (s (ring.rightNeighbor e)).si = offSI c.t) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hser := internalDoneDoneSerFrame
    (s e) (s (ring.rightNeighbor e)) hx hy hp ho hq
  have hstart := nonrootHardStartFalse
    (s e) (s (ring.rightNeighbor e)) hx
  have hghost := internalDoneDoneGhostFixed
    ring root s g e hstart ho hq
  have hclass : CoveredIdleClass ring root s g e :=
    { oldSourceOff := hsix
      oldTargetOff := hsiy
      serializerX := hser.1
      serializerY := hser.2
      ghostFixed := hghost }
  exact validationCoveredIdleClass
    ring root s g e shape hfixed hno hclass

end EWord
end L3

/-!
These certificates are not the complete
ValidationTransport and do not assert all-edge closure.

The two final theorems below are full-ValidationShape theorems
for explicitly guarded covered-idle subrows; they do not assert
the unrestricted coveredInside class.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! Native flags are read from POST-E, hence from the selected
pair in phiW.  WFixedRoot of the successor is the correct
hypothesis for deriving these flags. -/

theorem validationPostSourceNonroot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hne : e ≠ root) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l =
      false := by
  cases hb : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l with
  | false =>
      rfl
  | true =>
      have hlead : ((phiW ring s e) e).native.l =
          true := by
        rw [phiSource]
        exact hb
      exact False.elim (hne (hfixed.2.1 e hlead))

theorem validationPostTargetNonroot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hneq : ring.rightNeighbor e ≠ e)
    (hne : ring.rightNeighbor e ≠ root) :
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
      false := by
  cases hb : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l with
  | false =>
      rfl
  | true =>
      have hlead :
          ((phiW ring s e) (ring.rightNeighbor e)).native.l =
            true := by
        rw [phiResponder ring s e hneq]
        exact hb
      exact False.elim
        (hne (hfixed.2.1 (ring.rightNeighbor e) hlead))

theorem validationPostSourceRoot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (hfixed : WFixedRoot ring root (phiW ring s root)) :
    (postW (s root) (s (ring.rightNeighbor root))).eX.l =
      true := by
  have hr := hfixed.1
  rw [phiSource] at hr
  exact hr

theorem validationPostTargetRoot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hneq : ring.rightNeighbor e ≠ e)
    (hroot : ring.rightNeighbor e = root) :
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
      true := by
  have hr :
      ((phiW ring s e) (ring.rightNeighbor e)).native.l =
        true := by
    rw [hroot]
    exact hfixed.1
  rw [phiResponder ring s e hneq] at hr
  exact hr

/-! Literal serializer certificates of the outstanding rows.
These do not rely on arbitrary OLD SI or lease values. -/

/-- S2N: a nonroot B/NEW parent challenges C, B, or F. -/
theorem validationNewParentSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hb : x.ser.phase = .B)
    (hn : x.ser.out = .NEW)
    (hv : x.ser.wphase = .VALIDATING) :
    (serW x y).row = "S2N" ∧
    (serW x y).x.phase = .B ∧
    (serW x y).x.out = .WAIT ∧
    (serW x y).y.phase = .C ∧
    (serW x y).y.probe = .PENDING ∧
    (serW x y).y.wphase = .VALIDATING := by
  cases hphase : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hb, hn, hv, hphase, serChallengeWrite]

/-- S2N: an INTERNAL_OK answer admits a new broadcaster. -/
theorem validationInternalAdmissionSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hb : x.ser.phase = .B)
    (hw : x.ser.out = .WAIT)
    (hv : x.ser.wphase = .VALIDATING)
    (hc : y.ser.phase = .C)
    (hi : y.ser.probe = .INTERNAL_OK) :
    (serW x y).row = "S2N" ∧
    (serW x y).x.out = .DONE ∧
    (serW x y).y.phase = .B ∧
    (serW x y).y.out = .NEW ∧
    (serW x y).y.wphase = .VALIDATING := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hb, hw, hv, hc, hi, serEnterB]

/-- S2N: a LEAF_OK answer creates the return F. -/
theorem validationLeafAdmissionSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hb : x.ser.phase = .B)
    (hw : x.ser.out = .WAIT)
    (hc : y.ser.phase = .C)
    (hl : y.ser.probe = .LEAF_OK)
    (hoff : y.ser.wphase = .OFF) :
    (serW x y).row = "S2N" ∧
    (serW x y).x.out = .DONE ∧
    (serW x y).y.phase = .F ∧
    (serW x y).y.wphase = .OFF := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hb, hw, hc, hl, hoff, serEnterF]

/-- S3: a pending C sees a C on the right. -/
theorem validationPendingResponderSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.phase = .C)
    (hp : x.ser.probe = .PENDING)
    (hq : y.ser.phase = .C) :
    (serW x y).row = "S3" ∧
    (serW x y).x.phase = .C ∧
    (serW x y).x.probe = .INTERNAL_OK ∧
    (serW x y).x.wphase = x.ser.wphase ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hc, hp, hq]

/-- S5: a real pending leaf next to a running root is marked. -/
theorem validationSeamLeafSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hr : y.ser.cert = .RUNNING)
    (hc : x.ser.phase = .C)
    (hp : x.ser.probe = .PENDING) :
    (serW x y).row = "S5" ∧
    (serW x y).x.phase = .C ∧
    (serW x y).x.probe = .LEAF_OK ∧
    (serW x y).x.wphase = .OFF ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hr, hc, hp]

/-- S4: returned F on the right is canonically retired. -/
theorem validationReturnClearSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hf : x.ser.phase = .F)
    (hg : y.ser.phase = .F) :
    (serW x y).row = "S4" ∧
    (serW x y).x = x.ser ∧
    (serW x y).y.phase = .C ∧
    (serW x y).y.probe = .NONE ∧
    (serW x y).y.wphase = .OFF := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hf, hg, serCanonicalC]

/-! Two fully lifted *idle* covered subrows.  No additional
assumption on the unvisited part of the ring is made. -/

theorem validationNonBGhostFixed
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hp : (s e).ser.phase = .C ∨
      (s e).ser.phase = .F) :
    validationGhostStep ring root s g e = g := by
  rcases hp with hc | hf
  · cases hstage : g.stage <;>
      simp [validationGhostStep, hs, hstage, hc]
  · cases hstage : g.stage <;>
      simp [validationGhostStep, hs, hstage, hf]

theorem validationInternalFToCSerFrame {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hf : x.ser.phase = .F)
    (hc : y.ser.phase = .C) :
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hf, hc]

theorem validationInternalCNoneToCSerFrame {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.phase = .C)
    (hn : x.ser.probe = .NONE)
    (hq : y.ser.phase = .C) :
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hc, hn, hq]

/-- S4 F→C, full shape under literal INTERNAL flags and free SI. -/
theorem validationCoveredFToCFullShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = false)
    (hf : (s e).ser.phase = .F)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hsix : (s e).si = offSI c.t)
    (hsiy : (s (ring.rightNeighbor e)).si = offSI c.t) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hser := validationInternalFToCSerFrame
    (s e) (s (ring.rightNeighbor e)) hx hy hf hc
  have hstart := nonrootHardStartFalse
    (s e) (s (ring.rightNeighbor e)) hx
  have hghost := validationNonBGhostFixed
    ring root s g e hstart (Or.inr hf)
  have hclass : CoveredIdleClass ring root s g e :=
    { oldSourceOff := hsix
      oldTargetOff := hsiy
      serializerX := hser.1
      serializerY := hser.2
      ghostFixed := hghost }
  exact validationCoveredIdleClass
    ring root s g e shape hfixed hno hclass

/-- S3 C/NONE→C, full shape under literal INTERNAL flags
and free SI.  C/PENDING is intentionally NOT included. -/
theorem validationCoveredCNoneToCFullShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = false)
    (hc : (s e).ser.phase = .C)
    (hn : (s e).ser.probe = .NONE)
    (hq : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hsix : (s e).si = offSI c.t)
    (hsiy : (s (ring.rightNeighbor e)).si = offSI c.t) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hser := validationInternalCNoneToCSerFrame
    (s e) (s (ring.rightNeighbor e)) hx hy hc hn hq
  have hstart := nonrootHardStartFalse
    (s e) (s (ring.rightNeighbor e)) hx
  have hghost := validationNonBGhostFixed
    ring root s g e hstart (Or.inl hc)
  have hclass : CoveredIdleClass ring root s g e :=
    { oldSourceOff := hsix
      oldTargetOff := hsiy
      serializerX := hser.1
      serializerY := hser.2
      ghostFixed := hghost }
  exact validationCoveredIdleClass
    ring root s g e shape hfixed hno hclass

end EWord
end L3

/-!
Frontier-parent transport.
Every theorem uses only core Lean.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! The cyclic offset is a left inverse for offsets strictly below
n.  This avoids treating modular injectivity as a mere omega fact. -/

theorem validationSiteOffset {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (k : Nat) (hk : k < n) :
    PPL.cyclicOffset ring root (site ring root k) = k := by
  unfold PPL.cyclicOffset site PPL.shiftRight
  change (((root.val + k) % n + n - root.val) % n) = k
  by_cases hs : root.val + k < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        root.val + k + n - root.val = n + k := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hge : n ≤ root.val + k := by omega
    have hlt : root.val + k - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have heq :
        root.val + k - n + n - root.val = k := by
      omega
    rw [heq, Nat.mod_eq_of_lt hk]

theorem validationSiteInjective {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (h : site ring root i = site ring root j) :
    i = j := by
  have hc :=
    congrArg (fun z : Fin n => PPL.cyclicOffset ring root z) h
  rw [validationSiteOffset ring root i hi,
    validationSiteOffset ring root j hj] at hc
  exact hc

theorem validationParentNeighbor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (e : Fin n)
    (he : e = site ring root p) :
    ring.rightNeighbor e = site ring root (p + 1) := by
  rw [he]
  exact siteSuccessor ring root p

theorem validationParentSourceIff {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p k : Nat) (hp : p + 1 < n) (hk : k < n) :
    site ring root k = site ring root p ↔ k = p := by
  constructor
  · intro h
    exact validationSiteInjective ring root k p hk
      (by omega) h
  · intro h
    rw [h]

theorem validationParentTargetIff {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p k : Nat) (hp : p + 1 < n) (hk : k < n) :
    site ring root k =
      ring.rightNeighbor (site ring root p) ↔
      k = p + 1 := by
  constructor
  · intro h
    have h' : site ring root k =
        site ring root (p + 1) := by
      calc
        site ring root k =
            ring.rightNeighbor (site ring root p) := h
        _ = site ring root (p + 1) :=
          siteSuccessor ring root p
    exact validationSiteInjective ring root k (p + 1) hk hp h'
  · intro h
    rw [h]
    exact (siteSuccessor ring root p).symm

/-- The one-edge pointwise frame, with no assumption on
the serializer or SI fields outside the selected endpoints. -/
theorem validationParentFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (p : Nat) (e : Fin n)
    (hp : p + 1 < n) (he : e = site ring root p)
    (k : Nat) (hk : k < n)
    (hkp : k ≠ p) (hkc : k ≠ p + 1) :
    (phiW ring s e) (site ring root k) =
      s (site ring root k) := by
  apply remoteFrame ring s e (site ring root k)
  · intro h
    have h' : site ring root k = site ring root p := by
      simpa only [he] using h
    exact hkp
      ((validationParentSourceIff ring root p k hp hk).mp h')
  · intro h
    have h' :
        site ring root k =
          ring.rightNeighbor (site ring root p) := by
      simpa only [he] using h
    exact hkc
      ((validationParentTargetIff ring root p k hp hk).mp h')

theorem validationParentSourceAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (p : Nat) (e : Fin n)
    (he : e = site ring root p) :
    (phiW ring s e) (site ring root p) =
      (pairW (s e) (s (ring.rightNeighbor e))).1 := by
  calc
    (phiW ring s e) (site ring root p) =
        (phiW ring s e) e :=
      congrArg (phiW ring s e) he.symm
    _ = (pairW (s e) (s (ring.rightNeighbor e))).1 :=
      phiSource ring s e

theorem validationParentChildAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (p : Nat) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (he : e = site ring root p) :
    (phiW ring s e) (site ring root (p + 1)) =
      (pairW (s e) (s (ring.rightNeighbor e))).2 := by
  have hn := validationParentNeighbor ring root p e he
  calc
    (phiW ring s e) (site ring root (p + 1)) =
        (phiW ring s e) (ring.rightNeighbor e) :=
      congrArg (phiW ring s e) hn.symm
    _ = (pairW (s e) (s (ring.rightNeighbor e))).2 :=
      phiResponder ring s e hne

theorem validationParentSerializerAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (p : Nat) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (he : e = site ring root p) :
    ((phiW ring s e) (site ring root p)).ser =
      (serW (s e) (s (ring.rightNeighbor e))).x ∧
    ((phiW ring s e) (site ring root (p + 1))).ser =
      (serW (s e) (s (ring.rightNeighbor e))).y := by
  constructor
  · exact congrArg ProjW.ser
      (validationParentSourceAt ring root s p e he)
  · exact congrArg ProjW.ser
      (validationParentChildAt ring root s p e hne he)

/-! OLD forward-shape arithmetic and its covered prefix. -/

theorem validationForwardPivotCovered
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g) :
    g.pivot < g.scrub := by
  rcases hf.currentObligation with hn | hw
  · omega
  · omega

theorem validationParentOldSourceSI {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot) :
    (s e).si = offSI c.t := by
  have hk : g.pivot < n := by
    have := hf.pivotBound
    omega
  have hcov := validationForwardPivotCovered ring root s g hf
  have h := shape.scrubbed ⟨g.pivot, hk⟩ (by simpa using hcov)
  simpa only [he] using h

theorem validationParentOldChildSI {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hsc : g.scrub = g.pivot + 2) :
    (s (ring.rightNeighbor e)).si = offSI c.t := by
  have hcov : g.pivot + 1 < g.scrub := by omega
  have h := shape.scrubbed
    ⟨g.pivot + 1, hf.pivotBound⟩ (by simpa using hcov)
  simpa only [validationParentNeighbor ring root g.pivot e he]
    using h

theorem validationParentCompletedFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot) :
    ∀ i : Fin n, i.val < g.pivot →
      doneParent ring root (phiW ring s e) i.val := by
  intro i hi
  have hframe := validationParentFrame ring root s g.pivot e
    hf.pivotBound he i.val i.isLt (by omega) (by omega)
  unfold doneParent
  rw [hframe]
  exact hf.completed i hi

theorem validationParentCompletedExtend {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hdone : doneParent ring root (phiW ring s e) g.pivot) :
    ∀ i : Fin n, i.val < g.pivot + 1 →
      doneParent ring root (phiW ring s e) i.val := by
  intro i hi
  by_cases hp : i.val = g.pivot
  · simpa only [hp] using hdone
  · have hlt : i.val < g.pivot := by omega
    exact validationParentCompletedFrame ring root s g e hf he i hlt

theorem validationParentScrubPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hsrc :
      ((phiW ring s e) (site ring root g.pivot)).si = offSI c.t)
    (hchild :
      ((phiW ring s e)
        (site ring root (g.pivot + 1))).si = offSI c.t) :
    ∀ i : Fin n, i.val < g.pivot + 2 →
      ((phiW ring s e) (site ring root i.val)).si =
        offSI c.t := by
  intro i hi
  by_cases hlt : i.val < g.pivot
  · have hcovered := validationForwardPivotCovered ring root s g hf
    have hframe := validationParentFrame ring root s g.pivot e
      hf.pivotBound he i.val i.isLt (by omega) (by omega)
    rw [hframe]
    exact shape.scrubbed i (by omega)
  · by_cases hp : i.val = g.pivot
    · simpa only [hp] using hsrc
    · have hc : i.val = g.pivot + 1 := by omega
      simpa only [hc] using hchild

/-! The root is either the parent (pivot zero), or is framed.
Only cert and wphase of the parent source are needed. -/

theorem validationParentRootFields {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hcert : (serW (s e)
      (s (ring.rightNeighbor e))).x.cert = (s e).ser.cert)
    (hphase : (serW (s e)
      (s (ring.rightNeighbor e))).x.wphase =
        (s e).ser.wphase) :
    ((phiW ring s e) root).ser.cert = .RUNNING ∧
    ((phiW ring s e) root).ser.wphase = .VALIDATING := by
  by_cases hz : g.pivot = 0
  · have he0 : e = root := by
      calc
        e = site ring root g.pivot := he
        _ = site ring root 0 := by rw [hz]
        _ = root := siteZero ring root
    have hv : ((phiW ring s e) root).ser =
        (serW (s e) (s (ring.rightNeighbor e))).x := by
      calc
        ((phiW ring s e) root).ser =
            ((phiW ring s e) e).ser := by rw [he0]
        _ = (serW (s e) (s (ring.rightNeighbor e))).x := by
          exact congrArg ProjW.ser (phiSource ring s e)
    constructor
    · rw [hv, hcert, he0]
      exact shape.rootRunning
    · rw [hv, hphase, he0]
      exact shape.rootValidating
  · have hzero : 0 < n := by
      have := shape.width
      omega
    have hframe := validationParentFrame ring root s g.pivot e
      hf.pivotBound he 0 hzero (by omega) (by omega)
    have hr : (phiW ring s e) root = s root := by
      simpa only [siteZero] using hframe
    constructor
    · rw [hr]
      exact shape.rootRunning
    · rw [hr]
      exact shape.rootValidating

theorem validationParentRootFront {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hsourceB : (serW (s e)
      (s (ring.rightNeighbor e))).x.phase = .B)
    (hzero : g.pivot = 0 →
      (serW (s e) (s (ring.rightNeighbor e))).x.out = .WAIT ∨
      (serW (s e) (s (ring.rightNeighbor e))).y.phase = .B) :
    ((phiW ring s e) root).ser.out = .WAIT ∨
    ((phiW ring s e)
      (ring.rightNeighbor root)).ser.phase = .B := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by
      have := shape.width
      omega) e
  by_cases hz : g.pivot = 0
  · have he0 : e = root := by
      calc
        e = site ring root g.pivot := he
        _ = site ring root 0 := by rw [hz]
        _ = root := siteZero ring root
    rcases hzero hz with hw | hb
    · left
      have hp := congrArg ProjW.ser (phiSource ring s e)
      have hv : ((phiW ring s e) root).ser =
          (serW (s e) (s (ring.rightNeighbor e))).x := by
        rw [he0] at hp ⊢
        exact hp
      rw [hv]
      exact hw
    · right
      have hp := congrArg ProjW.ser
        (phiResponder ring s e hne)
      have hv :
          ((phiW ring s e) (ring.rightNeighbor root)).ser =
            (serW (s e) (s (ring.rightNeighbor e))).y := by
        rw [he0] at hp ⊢
        exact hp
      rw [hv]
      exact hb
  · rcases hf.rootFront with hw | hb
    · left
      have hzeroN : 0 < n := by
        have := shape.width
        omega
      have hframe := validationParentFrame ring root s g.pivot e
        hf.pivotBound he 0 hzeroN (by omega) (by omega)
      have hr : (phiW ring s e) root = s root := by
        simpa only [siteZero] using hframe
      rw [hr]
      exact hw
    · right
      by_cases hpone : g.pivot = 1
      · have heOne : e = site ring root 1 := by
          simpa only [hpone] using he
        have hs := congrArg ProjW.ser (phiSource ring s e)
        have hv :
            ((phiW ring s e)
              (ring.rightNeighbor root)).ser =
                (serW (s e)
                  (s (ring.rightNeighbor e))).x := by
          rw [heOne, siteOne] at hs ⊢
          exact hs
        rw [hv]
        exact hsourceB
      · have hone : 1 < n := by
          have := shape.width
          omega
        have hframe := validationParentFrame ring root s g.pivot e
          hf.pivotBound he 1 hone (by omega) (by omega)
        have hr :
            (phiW ring s e) (ring.rightNeighbor root) =
              s (ring.rightNeighbor root) := by
          simpa only [siteOne] using hframe
        rw [hr]
        exact hb

/-! Native post-E flags are derived from WFixedRoot, not guessed
from the OLD native coordinates. -/

theorem validationParentPostTargetFalse {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e = site ring root g.pivot) :
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
      false := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by
      have := shape.width
      omega) e
  have hnotroot : ring.rightNeighbor e ≠ root := by
    intro hr
    have hh : site ring root (g.pivot + 1) =
        site ring root 0 := by
      calc
        site ring root (g.pivot + 1) =
            ring.rightNeighbor e :=
          (validationParentNeighbor ring root g.pivot e he).symm
        _ = root := hr
        _ = site ring root 0 := (siteZero ring root).symm
    have hzero : 0 < n := by
      have := shape.width
      omega
    have hc := validationSiteInjective ring root
      (g.pivot + 1) 0 hf.pivotBound hzero hh
    omega
  exact validationPostTargetNonroot ring root s e
    hfixed hne hnotroot

theorem validationParentRootSourceCert {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hpost :
      (postW (s e) (s (ring.rightNeighbor e))).eX.l =
        true) :
    (s e).ser.cert = .RUNNING := by
  have hlead : ((phiW ring s e) e).native.l = true := by
    rw [phiSource]
    exact hpost
  have heroot : e = root := hfixed.2.1 e hlead
  rw [heroot]
  exact shape.rootRunning

theorem validationParentHardStartFalse {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e)) :
    (serW (s e) (s (ring.rightNeighbor e))).hard.hardS1 =
      false := by
  by_cases he : e = root
  · have hr : (s e).ser.cert = .RUNNING := by
      rw [he]
      exact shape.rootRunning
    simp [serW, serializerStep, ProjW.lift, hr]
  · have hx :=
      validationPostSourceNonroot ring root s e hfixed he
    exact nonrootHardStartFalse
      (s e) (s (ring.rightNeighbor e)) hx

/-! S2N and S2R share the same four parent-pair writers, once
postY is false and postX implies a RUNNING root certificate. -/

theorem validationParentNewWrite {c : Compiled}
    (x y : ProjW c)
    (hy : (postW x y).eY.l = false)
    (hroot : (postW x y).eX.l = true →
      x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hn : x.ser.out = .NEW)
    (hv : x.ser.wphase = .VALIDATING) :
    (serW x y).x = { x.ser with out := .WAIT } ∧
    (serW x y).y =
      { y.ser with phase := .C, out := .NEW, probe := .PENDING, wphase := .VALIDATING } := by
  cases hx : (postW x y).eX.l with
  | false =>
      cases hphase : y.ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hb, hn, hv, hphase, serChallengeWrite]
  | true =>
      have hr := hroot hx
      cases hphase : y.ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hr, hb, hn, hv, hphase, serChallengeWrite]

theorem validationParentPendingWrite {c : Compiled}
    (x y : ProjW c)
    (hy : (postW x y).eY.l = false)
    (hroot : (postW x y).eX.l = true →
      x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hw : x.ser.out = .WAIT)
    (hc : y.ser.phase = .C)
    (hp : y.ser.probe = .PENDING) :
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  cases hx : (postW x y).eX.l with
  | false =>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hb, hw, hc, hp]
  | true =>
      have hr := hroot hx
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hr, hb, hw, hc, hp]

theorem validationParentInternalWrite {c : Compiled}
    (x y : ProjW c)
    (hy : (postW x y).eY.l = false)
    (hroot : (postW x y).eX.l = true →
      x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hw : x.ser.out = .WAIT)
    (hv : x.ser.wphase = .VALIDATING)
    (hc : y.ser.phase = .C)
    (hi : y.ser.probe = .INTERNAL_OK) :
    (serW x y).x = { x.ser with out := .DONE } ∧
    (serW x y).y =
      { y.ser with phase := .B, out := .NEW, probe := .NONE, wphase := .VALIDATING } := by
  cases hx : (postW x y).eX.l with
  | false =>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hb, hw, hv, hc, hi, serEnterB]
  | true =>
      have hr := hroot hx
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hr, hb, hw, hv, hc, hi, serEnterB]

theorem validationParentLeafWrite {c : Compiled}
    (x y : ProjW c)
    (hy : (postW x y).eY.l = false)
    (hroot : (postW x y).eX.l = true →
      x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hw : x.ser.out = .WAIT)
    (hc : y.ser.phase = .C)
    (hl : y.ser.probe = .LEAF_OK) :
    (serW x y).x = { x.ser with out := .DONE } ∧
    (serW x y).y =
      { y.ser with phase := .F, probe := .NONE } := by
  cases hx : (postW x y).eX.l with
  | false =>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hb, hw, hc, hl, serEnterF]
  | true =>
      have hr := hroot hx
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hr, hb, hw, hc, hl, serEnterF]

/-! OLD ghost transitions on the parent edge, one equation each.
A hard S1 is excluded by the active RUNNING root or nonroot
post-E leader flag, even when the OLD lease is arbitrary. -/

theorem validationGhostParentNewEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hf : g.stage = .forward)
    (he : e = site ring root g.pivot)
    (hb : (s e).ser.phase = .B)
    (hn : (s e).ser.out = .NEW)
    (hv : (s e).ser.wphase = .VALIDATING)
    (hc : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardChallenge = true) :
    validationGhostStep ring root s g e =
      { g with scrub := g.scrub + 1 } := by
  subst he
  simp [validationGhostStep, hs, hf, hb, hn, hv, hc]

theorem validationGhostParentPendingEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hf : g.stage = .forward)
    (he : e = site ring root g.pivot)
    (hb : (s e).ser.phase = .B)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hp : (s (ring.rightNeighbor e)).ser.probe = .PENDING) :
    validationGhostStep ring root s g e = g := by
  subst he
  simp [validationGhostStep, hs, hf, hb, hw, hc, hp]

theorem validationGhostParentInternalEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hf : g.stage = .forward)
    (he : e = site ring root g.pivot)
    (hb : (s e).ser.phase = .B)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hi : (s (ring.rightNeighbor e)).ser.probe = .INTERNAL_OK) :
    validationGhostStep ring root s g e =
      { g with pivot := g.pivot + 1 } := by
  subst he
  simp [validationGhostStep, hs, hf, hb, hw, hc, hi]

theorem validationGhostParentLeafEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hf : g.stage = .forward)
    (he : e = site ring root g.pivot)
    (hb : (s e).ser.phase = .B)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hl : (s (ring.rightNeighbor e)).ser.probe = .LEAF_OK) :
    validationGhostStep ring root s g e =
      { g with stage := .returning, pivot := g.pivot + 1 } := by
  subst he
  simp [validationGhostStep, hs, hf, hb, hw, hc, hl]

theorem validationFrontierNewObligation {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g)
    (hn : (s (site ring root g.pivot)).ser.out = .NEW) :
    0 < g.pivot ∧ g.scrub = g.pivot + 1 := by
  rcases hf.currentObligation with ha | hb
  · exact ⟨ha.1, ha.2.2⟩
  · rw [hn] at hb
    cases hb.1

theorem validationFrontierWaitObligation {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g)
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT) :
    g.scrub = g.pivot + 2 ∧
      pendingChild ring root s g.pivot := by
  rcases hf.currentObligation with ha | hb
  · rw [hw] at ha
    cases ha.2.1
  · exact ⟨hb.2.1, hb.2.2⟩

/-! WAIT child-probe witnesses extracted from the actual forward
obligation; they exclude the other two pendingChild alternatives. -/

theorem validationFrontierWaitInternalWitness {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g)
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT)
    (hi : (s (site ring root (g.pivot + 1))).ser.probe =
      .INTERNAL_OK) :
    g.scrub = g.pivot + 2 ∧ g.pivot + 2 < n := by
  obtain ⟨hsc, hpc⟩ :=
    validationFrontierWaitObligation ring root s g hf hw
  unfold pendingChild at hpc
  rcases hpc with ⟨_, hpend | hinter | hleaf⟩
  · have hbad : SerProbe.PENDING = SerProbe.INTERNAL_OK :=
      hpend.1.symm.trans hi
    cases hbad
  · exact ⟨hsc, hinter.1⟩
  · have hbad : SerProbe.LEAF_OK = SerProbe.INTERNAL_OK :=
      hleaf.2.1.symm.trans hi
    cases hbad

theorem validationFrontierWaitLeafWitness {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g)
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT)
    (hl : (s (site ring root (g.pivot + 1))).ser.probe =
      .LEAF_OK) :
    g.scrub = g.pivot + 2 ∧
      g.pivot + 2 = n ∧
      (s (site ring root (g.pivot + 1))).ser.wphase = .OFF := by
  obtain ⟨hsc, hpc⟩ :=
    validationFrontierWaitObligation ring root s g hf hw
  unfold pendingChild at hpc
  rcases hpc with ⟨_, hpend | hinter | hleaf⟩
  · have hbad : SerProbe.PENDING = SerProbe.LEAF_OK :=
      hpend.1.symm.trans hl
    cases hbad
  · have hbad : SerProbe.INTERNAL_OK = SerProbe.LEAF_OK :=
      hinter.2.1.symm.trans hl
    cases hbad
  · exact ⟨hsc, hleaf.1, hleaf.2.2⟩

/-- Given actual serializer and SI endpoints, the only remaining
whole-shape work is the forward/return grammar for the new ghost. -/
theorem validationParentAssemble {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g g' : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hghost : validationGhostStep ring root s g e = g')
    (hfresh : g'.fresh = true)
    (hlower : 2 ≤ g'.scrub)
    (hupper : g'.scrub ≤ n)
    (hnear : g'.scrub ≤ g.pivot + 2)
    (hsiX : ((phiW ring s e)
      (site ring root g.pivot)).si = offSI c.t)
    (hsiY : ((phiW ring s e)
      (site ring root (g.pivot + 1))).si = offSI c.t)
    (hcert : (serW (s e)
      (s (ring.rightNeighbor e))).x.cert = (s e).ser.cert)
    (hwp : (serW (s e)
      (s (ring.rightNeighbor e))).x.wphase =
        (s e).ser.wphase)
    (hstage : ForwardShape ring root (phiW ring s e) g' ∨
      ReturnShape ring root (phiW ring s e) g') :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  rw [hghost]
  have hroot := validationParentRootFields
    ring root s g e shape hf he hcert hwp
  refine {
    genuine := hfresh
    protectedRoot := hfixed
    width := shape.width
    rootRunning := hroot.1
    rootValidating := hroot.2
    lower := hlower
    upper := hupper
    scrubbed := ?_
    stageShape := hstage }
  intro i hi
  exact validationParentScrubPrefix
    ring root s g e shape hf he hsiX hsiY i
      (Nat.lt_of_lt_of_le hi hnear)

/-! Case A: NEW parent challenges a fresh child.  The source must
be internal because ForwardShape allows NEW only for positive pivot. -/

theorem validationFrontierParentNewCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (_hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hn : (s e).ser.out = .NEW) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hnew : 0 < g.pivot ∧ g.scrub = g.pivot + 1 :=
    validationFrontierNewObligation ring root s g hf
      (by simpa only [he] using hn)
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (s e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by
      have := shape.width
      omega) e
  have hy := validationParentPostTargetFalse
    ring root s g e shape hf hfixed he
  have hroot := validationParentRootSourceCert
    ring root s g e shape hfixed
  have hw := validationParentNewWrite
    (s e) (s (ring.rightNeighbor e)) hy hroot hb hn hv
  have hloc := validationParentSerializerAt
    ring root s g.pivot e hne he
  have hxSer : ((phiW ring s e)
      (site ring root g.pivot)).ser =
        { (s e).ser with out := .WAIT } :=
    hloc.1.trans hw.1
  have hySer : ((phiW ring s e)
      (site ring root (g.pivot + 1))).ser =
        { (s (ring.rightNeighbor e)).ser with
          phase := .C, out := .NEW,
          probe := .PENDING, wphase := .VALIDATING } :=
    hloc.2.trans hw.2
  have hsi := frontierChallengeStep ring s e hne hb hn hv
  have hsiX : ((phiW ring s e)
      (site ring root g.pivot)).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si) he.symm
    exact ht.trans hsi.1
  have hsiY : ((phiW ring s e)
      (site ring root (g.pivot + 1))).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si)
      (validationParentNeighbor ring root g.pivot e he).symm
    exact ht.trans hsi.2
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hch := freshChildGuards
    (s e) (s (ring.rightNeighbor e)) hb hn hv
  have hg := validationGhostParentNewEq
    ring root s g e hstart hf.isForward he hb hn hv hch.1
  have hsourceB : (serW (s e)
      (s (ring.rightNeighbor e))).x.phase = .B := by
    rw [hw.1]
    exact hb
  have hrootFront : ((phiW ring s e) root).ser.out = .WAIT ∨
      ((phiW ring s e)
        (ring.rightNeighbor root)).ser.phase = .B :=
    validationParentRootFront ring root s g e shape hf he
      hsourceB (by intro hz; omega)
  have hobl := validationFrontierNewObligation ring root s g hf
    (by rw [← he]; exact hn)
  have hstage :
      ForwardShape ring root (phiW ring s e)
        { g with scrub := g.scrub + 1 } := by
    refine {
      isForward := hf.isForward
      pivotBound := hf.pivotBound
      completed := validationParentCompletedFrame
        ring root s g e hf he
      parentB := ?_
      parentValidating := ?_
      currentObligation := ?_
      rootFront := hrootFront }
    · rw [hxSer]
      exact hb
    · rw [hxSer]
      exact hv
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [hxSer]
      · change g.scrub + 1 = g.pivot + 2
        have := hobl.2
        omega
      · unfold pendingChild
        rw [hySer]
        exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hcert : (serW (s e)
      (s (ring.rightNeighbor e))).x.cert = (s e).ser.cert := by
    rw [hw.1]
  have hwp : (serW (s e)
      (s (ring.rightNeighbor e))).x.wphase =
        (s e).ser.wphase := by
    rw [hw.1]
  apply validationParentAssemble
    ring root s g { g with scrub := g.scrub + 1 } e
    shape hf he hfixed hg
  · exact shape.genuine
  · have := shape.lower
    dsimp only
    omega
  · have := hf.pivotBound
    have := hobl.2
    dsimp only
    omega
  · have := hobl.2
    dsimp only
    omega
  · exact hsiX
  · exact hsiY
  · exact hcert
  · exact hwp
  · exact Or.inl hstage

/-! Case B: WAIT/PENDING is a serializer frame.  Its two SI
records were already scrubbed on the preceding NEW challenge. -/

theorem validationFrontierParentPendingCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hp : (s (ring.rightNeighbor e)).ser.probe = .PENDING) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hsc := (validationFrontierWaitObligation
    ring root s g hf (by simpa only [he] using hw)).1
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hy := validationParentPostTargetFalse
    ring root s g e shape hf hfixed he
  have hroot := validationParentRootSourceCert
    ring root s g e shape hfixed
  have hpair := validationParentPendingWrite
    (s e) (s (ring.rightNeighbor e)) hy hroot hb hw hc hp
  have hsrcSI := validationParentOldSourceSI
    ring root s g e shape hf he
  have hdstSI := validationParentOldChildSI
    ring root s g e shape hf he hsc
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hg := validationGhostParentPendingEq
    ring root s g e hstart hf.isForward he hb hw hc hp
  have hclass : CoveredIdleClass ring root s g e :=
    { oldSourceOff := hsrcSI
      oldTargetOff := hdstSI
      serializerX := hpair.1
      serializerY := hpair.2
      ghostFixed := hg }
  exact validationCoveredIdleClass
    ring root s g e shape hfixed hno hclass

/-! Case C: WAIT/INTERNAL_OK promotes its admitted C child
to B/NEW and moves the pivot right by one. -/

theorem validationFrontierParentInternalCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hi : (s (ring.rightNeighbor e)).ser.probe = .INTERNAL_OK)
    (hbound : g.pivot + 2 < n) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hchildProbe :
      (s (site ring root (g.pivot + 1))).ser.probe =
        .INTERNAL_OK := by
    rw [← validationParentNeighbor ring root g.pivot e he]
    exact hi
  have hobl := validationFrontierWaitInternalWitness
    ring root s g hf (by rw [← he]; exact hw) hchildProbe
  have hsc : g.scrub = g.pivot + 2 := hobl.1
  have hboundFromWitness : g.pivot + 2 < n := hobl.2
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (s e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by
      have := shape.width
      omega) e
  have hy := validationParentPostTargetFalse
    ring root s g e shape hf hfixed he
  have hroot := validationParentRootSourceCert
    ring root s g e shape hfixed
  have hpair := validationParentInternalWrite
    (s e) (s (ring.rightNeighbor e))
    hy hroot hb hw hv hc hi
  have hloc := validationParentSerializerAt
    ring root s g.pivot e hne he
  have hxSer : ((phiW ring s e)
      (site ring root g.pivot)).ser =
        { (s e).ser with out := .DONE } :=
    hloc.1.trans hpair.1
  have hySer : ((phiW ring s e)
      (site ring root (g.pivot + 1))).ser =
        { (s (ring.rightNeighbor e)).ser with
          phase := .B, out := .NEW,
          probe := .NONE, wphase := .VALIDATING } :=
    hloc.2.trans hpair.2
  have hsrcOld := validationParentOldSourceSI
    ring root s g e shape hf he
  have hdstOld := validationParentOldChildSI
    ring root s g e shape hf he hsc
  have hsi := coveredPairStep ring s e hne
    hsrcOld hdstOld hno
  have hsiX : ((phiW ring s e)
      (site ring root g.pivot)).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si) he.symm
    exact ht.trans hsi.1
  have hsiY : ((phiW ring s e)
      (site ring root (g.pivot + 1))).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si)
      (validationParentNeighbor ring root g.pivot e he).symm
    exact ht.trans hsi.2
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hg := validationGhostParentInternalEq
    ring root s g e hstart hf.isForward he hb hw hc hi
  have hdone : doneParent ring root
      (phiW ring s e) g.pivot := by
    unfold doneParent
    rw [hxSer]
    exact ⟨hb, rfl, hv⟩
  have hsourceB : (serW (s e)
      (s (ring.rightNeighbor e))).x.phase = .B := by
    rw [hpair.1]
    exact hb
  have hrootFront : ((phiW ring s e) root).ser.out = .WAIT ∨
      ((phiW ring s e)
        (ring.rightNeighbor root)).ser.phase = .B :=
    validationParentRootFront ring root s g e shape hf he
      hsourceB (by
        intro _
        right
        rw [hpair.2])
  have hstage :
      ForwardShape ring root (phiW ring s e)
        { g with pivot := g.pivot + 1 } := by
    refine {
      isForward := hf.isForward
      pivotBound := by omega
      completed := validationParentCompletedExtend
        ring root s g e hf he hdone
      parentB := ?_
      parentValidating := ?_
      currentObligation := ?_
      rootFront := hrootFront }
    · rw [hySer]
    · rw [hySer]
    · left
      refine ⟨?_, ?_, ?_⟩
      · change 0 < g.pivot + 1
        omega
      · rw [hySer]
      · change g.scrub = (g.pivot + 1) + 1
        have := hsc
        omega
  have hcert : (serW (s e)
      (s (ring.rightNeighbor e))).x.cert = (s e).ser.cert := by
    rw [hpair.1]
  have hwp : (serW (s e)
      (s (ring.rightNeighbor e))).x.wphase =
        (s e).ser.wphase := by
    rw [hpair.1]
  apply validationParentAssemble
    ring root s g { g with pivot := g.pivot + 1 } e
    shape hf he hfixed hg
  · exact shape.genuine
  · exact shape.lower
  · exact shape.upper
  · change g.scrub ≤ g.pivot + 2
    omega
  · exact hsiX
  · exact hsiY
  · exact hcert
  · exact hwp
  · exact Or.inl hstage

/-! Case D: WAIT/LEAF_OK is the actual transition from the
forward grammar into the returning suffix grammar. -/

theorem validationFrontierParentLeafCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root g.pivot)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hw : (s e).ser.out = .WAIT)
    (hc : (s (ring.rightNeighbor e)).ser.phase = .C)
    (hl : (s (ring.rightNeighbor e)).ser.probe = .LEAF_OK)
    (hoff : (s (ring.rightNeighbor e)).ser.wphase = .OFF)
    (hlast : g.pivot + 2 = n) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hchildProbe :
      (s (site ring root (g.pivot + 1))).ser.probe =
        .LEAF_OK := by
    rw [← validationParentNeighbor ring root g.pivot e he]
    exact hl
  have hobl := validationFrontierWaitLeafWitness
    ring root s g hf (by rw [← he]; exact hw) hchildProbe
  have hsc : g.scrub = g.pivot + 2 := hobl.1
  have hlastFromWitness : g.pivot + 2 = n := hobl.2.1
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (s e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by
      have := shape.width
      omega) e
  have hy := validationParentPostTargetFalse
    ring root s g e shape hf hfixed he
  have hroot := validationParentRootSourceCert
    ring root s g e shape hfixed
  have hpair := validationParentLeafWrite
    (s e) (s (ring.rightNeighbor e))
    hy hroot hb hw hc hl
  have hloc := validationParentSerializerAt
    ring root s g.pivot e hne he
  have hxSer : ((phiW ring s e)
      (site ring root g.pivot)).ser =
        { (s e).ser with out := .DONE } :=
    hloc.1.trans hpair.1
  have hySer : ((phiW ring s e)
      (site ring root (g.pivot + 1))).ser =
        { (s (ring.rightNeighbor e)).ser with
          phase := .F, probe := .NONE } :=
    hloc.2.trans hpair.2
  have hsrcOld := validationParentOldSourceSI
    ring root s g e shape hf he
  have hdstOld := validationParentOldChildSI
    ring root s g e shape hf he hsc
  have hsi := coveredPairStep ring s e hne
    hsrcOld hdstOld hno
  have hsiX : ((phiW ring s e)
      (site ring root g.pivot)).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si) he.symm
    exact ht.trans hsi.1
  have hsiY : ((phiW ring s e)
      (site ring root (g.pivot + 1))).si = offSI c.t := by
    have ht := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si)
      (validationParentNeighbor ring root g.pivot e he).symm
    exact ht.trans hsi.2
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hg := validationGhostParentLeafEq
    ring root s g e hstart hf.isForward he hb hw hc hl
  have hdone : doneParent ring root
      (phiW ring s e) g.pivot := by
    unfold doneParent
    rw [hxSer]
    exact ⟨hb, rfl, hv⟩
  have hstage :
      ReturnShape ring root (phiW ring s e)
        { g with stage := .returning, pivot := g.pivot + 1 } := by
    refine {
      isReturn := rfl
      covered := by
        change g.scrub = n
        exact hsc.trans hlastFromWitness
      pivotPositive := by
        change 0 < g.pivot + 1
        omega
      pivotBound := hf.pivotBound
      completed := validationParentCompletedExtend
        ring root s g e hf he hdone
      leftmostF := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · rw [hySer]
    · have heq : (g.pivot + 1) + 1 = n := by omega
      change ((phiW ring s e)
        (site ring root (g.pivot + 1))).ser.wphase =
          (if (g.pivot + 1) + 1 = n then .OFF else .CURRENT)
      rw [hySer, if_pos heq]
      exact hoff
    · intro i hi
      change g.pivot + 1 < i.val at hi
      have hlt : i.val < n := i.isLt
      have hmax : g.pivot + 2 = n := hlastFromWitness
      have hfalse : False := by omega
      exact False.elim hfalse
  have hcert : (serW (s e)
      (s (ring.rightNeighbor e))).x.cert = (s e).ser.cert := by
    rw [hpair.1]
  have hwp : (serW (s e)
      (s (ring.rightNeighbor e))).x.wphase =
        (s e).ser.wphase := by
    rw [hpair.1]
  apply validationParentAssemble
    ring root s g
      { g with stage := .returning, pivot := g.pivot + 1 } e
    shape hf he hfixed hg
  · exact shape.genuine
  · exact shape.lower
  · exact shape.upper
  · change g.scrub ≤ g.pivot + 2
    omega
  · exact hsiX
  · exact hsiY
  · exact hcert
  · exact hwp
  · exact Or.inr hstage

/-- Full requested frontier-parent class, after the priority
classifier has selected the genuinely forward parent edge.
Includes the root S2R (pivot zero) and internal S2N rows. -/
theorem validationFrontierParentClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hclass : validationEdgeClass ring root g e =
      .frontierParent) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hp : g.stage = .forward ∧
      e = site ring root g.pivot := by
    unfold validationEdgeClass at hclass
    by_cases hs : e = site ring root (n - 1)
    · rw [if_pos hs] at hclass
      cases hclass
    · rw [if_neg hs] at hclass
      by_cases ht : g.stage = .forward ∧
          e = site ring root g.pivot
      · exact ht
      · rw [if_neg ht] at hclass
        by_cases hc : g.stage = .forward ∧
            e = site ring root (g.pivot + 1)
        · rw [if_pos hc] at hclass
          cases hclass
        · rw [if_neg hc] at hclass
          by_cases hr : ∀ i : Fin n, i.val < g.scrub →
              site ring root i.val ≠ e ∧
              site ring root i.val ≠ ring.rightNeighbor e
          · rw [if_pos hr] at hclass
            cases hclass
          · rw [if_neg hr] at hclass
            cases hclass
  have he := hp.2
  have hf : ForwardShape ring root s g := by
    rcases shape.stageShape with hf | hr
    · exact hf
    · have hbad : False := by
        rw [hr.isReturn] at hp
        cases hp.1
      exact False.elim hbad
  have hn := validationParentNeighbor
    ring root g.pivot e he
  rcases hf.currentObligation with hnew | hwait
  · have ho : (s e).ser.out = .NEW := by
      rw [he]
      exact hnew.2.1
    exact validationFrontierParentNewCase
      ring root s g e shape hf he hfixed hno ho
  · have ho : (s e).ser.out = .WAIT := by
      rw [he]
      exact hwait.1
    unfold pendingChild at hwait
    have hc : (s (ring.rightNeighbor e)).ser.phase = .C := by
      rw [hn]
      exact hwait.2.2.1
    rcases hwait.2.2.2 with
      hpend | hinternal | hleaf
    · have hprobe :
          (s (ring.rightNeighbor e)).ser.probe =
            .PENDING := by
        rw [hn]
        exact hpend.1
      exact validationFrontierParentPendingCase
        ring root s g e shape hf he hfixed hno
        ho hc hprobe
    · have hprobe :
          (s (ring.rightNeighbor e)).ser.probe =
            .INTERNAL_OK := by
        rw [hn]
        exact hinternal.2.1
      exact validationFrontierParentInternalCase
        ring root s g e shape hf he hfixed hno
        ho hc hprobe hinternal.1
    · have hprobe :
          (s (ring.rightNeighbor e)).ser.probe =
            .LEAF_OK := by
        rw [hn]
        exact hleaf.2.1
      have hwp :
          (s (ring.rightNeighbor e)).ser.wphase =
            .OFF := by
        rw [hn]
        exact hleaf.2.2
      exact validationFrontierParentLeafCase
        ring root s g e shape hf he hfixed hno
        ho hc hprobe hwp hleaf.1

end EWord
end L3

/-!
Child-service transport.
The class excludes the last physical edge by rootSeam priority.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! Geometry: a child service starts at pivot+1 and targets
pivot+2. The latter is not the root within this class. -/

theorem validationChildNeighbor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (e : Fin n)
    (he : e = site ring root (p + 1)) :
    ring.rightNeighbor e = site ring root (p + 2) := by
  rw [he]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (siteSuccessor ring root (p + 1))

theorem validationChildFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (p : Nat) (e : Fin n)
    (hbound : p + 2 < n)
    (he : e = site ring root (p + 1))
    (k : Nat) (hk : k < n)
    (hsrc : k ≠ p + 1) (hdst : k ≠ p + 2) :
    (phiW ring s e) (site ring root k) =
      s (site ring root k) := by
  apply validationParentFrame ring root s (p + 1) e
    (by omega) he k hk hsrc
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hdst

theorem validationChildNoSeamBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hp : p + 1 < n)
    (he : e = site ring root (p + 1))
    (hs : e ≠ site ring root (n - 1)) :
    p + 2 < n := by
  by_cases h : p + 2 < n
  · exact h
  · have hlast : p + 1 = n - 1 := by omega
    have hbad : e = site ring root (n - 1) := by
      rw [he, hlast]
    exact False.elim (hs hbad)

theorem validationChildNotRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hp : p + 1 < n)
    (he : e = site ring root (p + 1)) :
    e ≠ root := by
  intro h
  have hs : site ring root (p + 1) =
      site ring root 0 := by
    calc
      site ring root (p + 1) = e := he.symm
      _ = root := h
      _ = site ring root 0 := (siteZero ring root).symm
  have hzero : 0 < n := by omega
  have hx := validationSiteInjective ring root
    (p + 1) 0 hp hzero hs
  omega

theorem validationChildTargetNotRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hbound : p + 2 < n)
    (he : e = site ring root (p + 1)) :
    ring.rightNeighbor e ≠ root := by
  intro h
  have hs : site ring root (p + 2) =
      site ring root 0 := by
    calc
      site ring root (p + 2) =
          ring.rightNeighbor e :=
        (validationChildNeighbor ring root p e he).symm
      _ = root := h
      _ = site ring root 0 := (siteZero ring root).symm
  have hzero : 0 < n := by omega
  have hx := validationSiteInjective ring root
    (p + 2) 0 hbound hzero hs
  omega

theorem validationChildPostFlags {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hp : p + 1 < n)
    (hbound : p + 2 < n)
    (he : e = site ring root (p + 1))
    (hfixed : WFixedRoot ring root (phiW ring s e)) :
    (postW (s e) (s (ring.rightNeighbor e))).eX.l =
        false ∧
    (postW (s e) (s (ring.rightNeighbor e))).eY.l =
        false := by
  have hs := validationChildNotRoot ring root p e hn hp he
  have ht := validationChildTargetNotRoot ring root p e hn
    hbound he
  have hneq : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by omega) e
  exact ⟨validationPostSourceNonroot ring root s e hfixed hs,
    validationPostTargetNonroot ring root s e hfixed hneq ht⟩

/-- The proof ghost does not react at a child edge. In
particular this includes arbitrary inherited child bytes before
the parent has issued its NEW challenge. -/
theorem validationGhostChildEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (g : ValidationGhost) (e : Fin n)
    (hn : 3 ≤ n)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root (g.pivot + 1)) :
    validationGhostStep ring root s g e = g := by
  have hnotroot := validationChildNotRoot ring root g.pivot e
    hn hf.pivotBound he
  have hnotparent : e ≠ site ring root g.pivot := by
    intro h
    have hsite : site ring root (g.pivot + 1) =
        site ring root g.pivot := by
      calc
        site ring root (g.pivot + 1) = e := he.symm
        _ = site ring root g.pivot := h
    have hlt : g.pivot < n := by
      have := hf.pivotBound
      omega
    have hbad := validationSiteInjective ring root
      (g.pivot + 1) g.pivot hf.pivotBound hlt hsite
    omega
  simp [validationGhostStep, hnotroot, hf.isForward,
    hnotparent]

/-! The remaining S3 row certificates. They use POST-E flags,
rather than assumptions on OLD native leader bits. -/

/-- When a covered child sees B or F ahead, that responder
is canonicalized to C/OFF and the child itself is unchanged. -/
theorem validationChildCanonicalSerializer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.phase = .C)
    (hr : y.ser.phase = .B ∨ y.ser.phase = .F) :
    (serW x y).row = "S3" ∧
    (serW x y).x = x.ser ∧
    (serW x y).y = serCanonicalC y.ser := by
  rcases hr with hb | hf
  · cases hp : x.ser.probe <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hc, hb, hp, serCanonicalC]
  · cases hp : x.ser.probe <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hc, hf, hp, serCanonicalC]

/-- An already-observed INTERNAL_OK child sees C: S3 frames
both selected serializer records. -/
theorem validationChildAnsweredFrame {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.phase = .C)
    (hi : x.ser.probe = .INTERNAL_OK)
    (hr : y.ser.phase = .C) :
    (serW x y).row = "S3" ∧
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hc, hi, hr]

/-- S3 leaves a pending C pending when the responder is B/F,
or observes INTERNAL_OK when the responder is C.
An already INTERNAL_OK source stays INTERNAL_OK. -/
theorem validationChildSerializerInvariant {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hc : x.ser.phase = .C)
    (hv : x.ser.wphase = .VALIDATING)
    (hp : x.ser.probe = .PENDING ∨
      x.ser.probe = .INTERNAL_OK) :
    (serW x y).x.phase = .C ∧
    (serW x y).x.wphase = .VALIDATING ∧
    ((serW x y).x.probe = .PENDING ∨
      (serW x y).x.probe = .INTERNAL_OK) := by
  rcases hp with hpend | hint
  · cases hright : y.ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hc, hv, hpend, hright, serCanonicalC]
  · cases hright : y.ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hc, hv, hint, hright, serCanonicalC]

/-! WAIT obligations are causal, whereas NEW has no constraint
on the serializer or SI of the not-yet-challenged child. -/

theorem validationChildWaitSource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (hf : ForwardShape ring root s g)
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT)
    (hbound : g.pivot + 2 < n) :
    g.scrub = g.pivot + 2 ∧
    (s (site ring root (g.pivot + 1))).ser.phase = .C ∧
    (s (site ring root (g.pivot + 1))).ser.wphase =
      .VALIDATING ∧
    ((s (site ring root (g.pivot + 1))).ser.probe =
        .PENDING ∨
      (s (site ring root (g.pivot + 1))).ser.probe =
        .INTERNAL_OK) := by
  obtain ⟨hsc, hpc⟩ :=
    validationFrontierWaitObligation ring root s g hf hw
  unfold pendingChild at hpc
  rcases hpc with ⟨hc, hp | hi | hl⟩
  · exact ⟨hsc, hc, hp.2, Or.inl hp.1⟩
  · exact ⟨hsc, hc, hi.2.2, Or.inr hi.2.1⟩
  · have hfalse : False := by
      have := hl.1
      omega
    exact False.elim hfalse

theorem validationChildNewPending {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hbound : p + 2 < n)
    (he : e = site ring root (p + 1))
    (hser :
      (serW (s e) (s (ring.rightNeighbor e))).x.phase = .C ∧
      (serW (s e) (s (ring.rightNeighbor e))).x.wphase =
        .VALIDATING ∧
      ((serW (s e)
        (s (ring.rightNeighbor e))).x.probe = .PENDING ∨
       (serW (s e)
        (s (ring.rightNeighbor e))).x.probe = .INTERNAL_OK)) :
    pendingChild ring root (phiW ring s e) p := by
  have hneq : ring.rightNeighbor e ≠ e :=
    rightNeighborDifferent ring (by omega) e
  have hloc := (validationParentSerializerAt
    ring root s (p + 1) e hneq he).1
  unfold pendingChild
  rw [hloc]
  rcases hser.2.2 with hp | hi
  · exact ⟨hser.1, Or.inl ⟨hp, hser.2.1⟩⟩
  · exact ⟨hser.1,
      Or.inr (Or.inl ⟨hbound, hi, hser.2.1⟩)⟩

theorem validationChildRootFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (p : Nat) (e : Fin n)
    (hn : 3 ≤ n)
    (hbound : p + 2 < n)
    (he : e = site ring root (p + 1)) :
    (phiW ring s e) root = s root := by
  have hzero : 0 < n := by omega
  have hfr := validationChildFrame ring root s p e
    hbound he 0 hzero (by omega) (by omega)
  simpa only [siteZero] using hfr

theorem validationChildWaitRootFront {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (g : ValidationGhost) (e : Fin n)
    (hn : 3 ≤ n)
    (hf : ForwardShape ring root s g)
    (hbound : g.pivot + 2 < n)
    (he : e = site ring root (g.pivot + 1))
    (hchild : (s (site ring root
      (g.pivot + 1))).ser.phase = .C) :
    ((phiW ring s e) root).ser.out = .WAIT ∨
    ((phiW ring s e)
      (ring.rightNeighbor root)).ser.phase = .B := by
  have hr := validationChildRootFrame ring root s g.pivot e
    hn hbound he
  by_cases hzero : g.pivot = 0
  · have hrootWait : (s root).ser.out = .WAIT := by
      rcases hf.rootFront with hw | hb
      · exact hw
      · have hcOne :
            (s (ring.rightNeighbor root)).ser.phase =
              .C := by
          simpa only [hzero, Nat.zero_add, siteOne]
            using hchild
        rw [hcOne] at hb
        cases hb
    left
    rw [hr]
    exact hrootWait
  · have hone : 1 < n := by omega
    have hfr := validationChildFrame ring root s g.pivot e
      hbound he 1 hone (by omega) (by omega)
    have hfirst :
        (phiW ring s e) (ring.rightNeighbor root) =
          s (ring.rightNeighbor root) := by
      simpa only [siteOne] using hfr
    rcases hf.rootFront with hw | hb
    · left
      rw [hr]
      exact hw
    · right
      rw [hfirst]
      exact hb

theorem validationChildWaitScrub {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (g : ValidationGhost) (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hbound : g.pivot + 2 < n)
    (he : e = site ring root (g.pivot + 1))
    (hsc : g.scrub = g.pivot + 2)
    (hchild :
      ((phiW ring s e)
        (site ring root (g.pivot + 1))).si = offSI c.t) :
    ∀ i : Fin n, i.val < g.scrub →
      ((phiW ring s e) (site ring root i.val)).si =
        offSI c.t := by
  intro i hi
  by_cases hidx : i.val = g.pivot + 1
  · simpa only [hidx] using hchild
  · have hdst : i.val ≠ g.pivot + 2 := by omega
    have hfr := validationChildFrame ring root s g.pivot
      e hbound he i.val i.isLt hidx hdst
    rw [hfr]
    exact shape.scrubbed i hi

/-- Lifting an S3 child update: the parent, all completed sites,
and the root are remote. The child is re-certified as pendingChild
after the pair; its selected SI remains off by the hard-left barrier. -/
theorem validationChildWaitTransportCore
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hbound : g.pivot + 2 < n)
    (he : e = site ring root (g.pivot + 1))
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT)
    (hsc : g.scrub = g.pivot + 2)
    (hchildOld :
      (s (site ring root (g.pivot + 1))).ser.phase = .C)
    (hchildNew :
      pendingChild ring root (phiW ring s e) g.pivot)
    (hchildSI :
      ((phiW ring s e)
        (site ring root (g.pivot + 1))).si = offSI c.t)
    (hg : validationGhostStep ring root s g e = g) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  rw [hg]
  have hroot := validationChildRootFrame ring root s g.pivot e
    shape.width hbound he
  have hparent := validationChildFrame ring root s g.pivot e
    hbound he g.pivot (by
      have := hf.pivotBound
      omega) (by omega) (by omega)
  have hrootFront := validationChildWaitRootFront
    ring root s g e shape.width hf hbound he hchildOld
  have hdone : ∀ i : Fin n, i.val < g.pivot →
      doneParent ring root (phiW ring s e) i.val := by
    intro i hi
    have hfr := validationChildFrame ring root s g.pivot e
      hbound he i.val i.isLt (by omega) (by omega)
    unfold doneParent
    rw [hfr]
    exact hf.completed i hi
  have hforward :
      ForwardShape ring root (phiW ring s e) g := by
    refine {
      isForward := hf.isForward
      pivotBound := hf.pivotBound
      completed := hdone
      parentB := ?_
      parentValidating := ?_
      currentObligation := ?_
      rootFront := hrootFront }
    · rw [hparent]
      exact hf.parentB
    · rw [hparent]
      exact hf.parentValidating
    · right
      refine ⟨?_, hsc, hchildNew⟩
      rw [hparent]
      exact hw
  refine {
    genuine := shape.genuine
    protectedRoot := hfixed
    width := shape.width
    rootRunning := ?_
    rootValidating := ?_
    lower := shape.lower
    upper := shape.upper
    scrubbed := ?_
    stageShape := Or.inl hforward }
  · rw [hroot]
    exact shape.rootRunning
  · rw [hroot]
    exact shape.rootValidating
  · exact validationChildWaitScrub
      ring root s g e shape hbound he hsc hchildSI

/-! The NEW case does not require a C child. The two endpoints
of this edge are both beyond the then-covered prefix. -/

theorem validationChallengedChildNewCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root (g.pivot + 1))
    (hbound : g.pivot + 2 < n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hsc : g.scrub = g.pivot + 1) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hg := validationGhostChildEq
    ring root s g e shape.width hf he
  rw [hg]
  apply validationCoveredSerSIFrame
    ring root s g e shape hfixed
  · intro i hi
    have hlt : i.val < g.pivot + 1 := by
      rw [hsc] at hi
      exact hi
    have hfr := validationChildFrame ring root s g.pivot e
      hbound he i.val i.isLt (by omega) (by omega)
    exact congrArg ProjW.ser hfr
  · intro i hi
    have hlt : i.val < g.pivot + 1 := by
      rw [hsc] at hi
      exact hi
    have hfr := validationChildFrame ring root s g.pivot e
      hbound he i.val i.isLt (by omega) (by omega)
    exact congrArg ProjW.si hfr

/-! WAIT case. It covers both actual observation
(C/PENDING+C) and the source-preserving S3 subrows
(C/PENDING or INTERNAL_OK with B/F responder, or INTERNAL_OK+C). -/

theorem validationChallengedChildWaitCase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (he : e = site ring root (g.pivot + 1))
    (hbound : g.pivot + 2 < n)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hw : (s (site ring root g.pivot)).ser.out = .WAIT) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hold := validationChildWaitSource
    ring root s g hf hw hbound
  have hsc : g.scrub = g.pivot + 2 := hold.1
  have hchildOld :
      (s (site ring root (g.pivot + 1))).ser.phase =
        .C := hold.2.1
  have hchildVal :
      (s (site ring root (g.pivot + 1))).ser.wphase =
        .VALIDATING := hold.2.2.1
  have hchildProbe :
      (s (site ring root (g.pivot + 1))).ser.probe =
        .PENDING ∨
      (s (site ring root (g.pivot + 1))).ser.probe =
        .INTERNAL_OK := hold.2.2.2
  have hx : (s e).ser.phase = .C := by
    rw [he]
    exact hchildOld
  have hv : (s e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hchildVal
  have hp : (s e).ser.probe = .PENDING ∨
      (s e).ser.probe = .INTERNAL_OK := by
    rw [he]
    exact hchildProbe
  have hpost := validationChildPostFlags
    ring root s g.pivot e shape.width hf.pivotBound
    hbound he hfixed
  have hser := validationChildSerializerInvariant
    (s e) (s (ring.rightNeighbor e))
    hpost.1 hpost.2 hx hv hp
  have hnewChild := validationChildNewPending
    ring root s g.pivot e shape.width hbound he hser
  have hsi := frontierLeftStep ring s e hv hno
  have hchildSI :
      ((phiW ring s e)
        (site ring root (g.pivot + 1))).si =
          offSI c.t := by
    have hindex := congrArg
      (fun k : Fin n => ((phiW ring s e) k).si) he.symm
    exact hindex.trans hsi
  have hg := validationGhostChildEq
    ring root s g e shape.width hf he
  exact validationChildWaitTransportCore
    ring root s g e shape hf hfixed hbound he
    hw hsc hchildOld hnewChild hchildSI hg

/-- Full-ValidationShape challengedChild transport. The priority
classifier excludes the incoming root seam at offset n-1.
No inherited bytes of an unvisited child are restricted. -/
theorem validationChallengedChildClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hclass : validationEdgeClass ring root g e =
      .challengedChild) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hnotSeam : e ≠ site ring root (n - 1) := by
    intro hs
    unfold validationEdgeClass at hclass
    rw [if_pos hs] at hclass
    cases hclass
  have hp : g.stage = .forward ∧
      e = site ring root (g.pivot + 1) := by
    unfold validationEdgeClass at hclass
    rw [if_neg hnotSeam] at hclass
    by_cases hpar : g.stage = .forward ∧
        e = site ring root g.pivot
    · rw [if_pos hpar] at hclass
      cases hclass
    · rw [if_neg hpar] at hclass
      by_cases hc : g.stage = .forward ∧
          e = site ring root (g.pivot + 1)
      · exact hc
      · rw [if_neg hc] at hclass
        by_cases hr : ∀ i : Fin n, i.val < g.scrub →
            site ring root i.val ≠ e ∧
            site ring root i.val ≠ ring.rightNeighbor e
        · rw [if_pos hr] at hclass
          cases hclass
        · rw [if_neg hr] at hclass
          cases hclass
  have hf : ForwardShape ring root s g := by
    rcases shape.stageShape with hf | hr
    · exact hf
    · have hbad : False := by
        rw [hr.isReturn] at hp
        cases hp.1
      exact False.elim hbad
  have hbound : g.pivot + 2 < n :=
    validationChildNoSeamBound ring root g.pivot e
      shape.width hf.pivotBound hp.2 hnotSeam
  rcases hf.currentObligation with hnew | hwait
  · exact validationChallengedChildNewCase
      ring root s g e shape hf hp.2 hbound hfixed hnew.2.2
  · exact validationChallengedChildWaitCase
      ring root s g e shape hf hp.2 hbound hfixed hno
      hwait.1

end EWord
end L3

/-!
Incoming root seam transport and additional covered-row
certificates. The missing coveredInside class and
assembly are deliberately not asserted.
-/

namespace L3
namespace EWord

set_option autoImplicit false

/-! ROOT_IN geometry: offset n-1 is the predecessor of root. -/

theorem validationSeamPeriod {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    site ring root n = root := by
  apply Fin.ext
  change (root.val + n) % n = root.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

theorem validationSeamNeighbor {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (he : e = site ring root (n - 1)) :
    ring.rightNeighbor e = root := by
  rw [he, siteSuccessor]
  have hn : n - 1 + 1 = n := by
    have := ring.hn
    omega
  rw [hn, validationSeamPeriod]

theorem validationSeamNotRoot {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 3 ≤ n)
    (he : e = site ring root (n - 1)) :
    e ≠ root := by
  intro h
  have hs : site ring root (n - 1) =
      site ring root 0 := by
    calc
      site ring root (n - 1) = e := he.symm
      _ = root := h
      _ = site ring root 0 := (siteZero ring root).symm
  have hbad := validationSiteInjective ring root
    (n - 1) 0 (by omega) (by omega) hs
  omega

theorem validationSeamFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n)
    (he : e = site ring root (n - 1))
    (k : Nat) (hk : k + 1 < n) (hpositive : 0 < k) :
    (phiW ring s e) (site ring root k) =
      s (site ring root k) := by
  have hneigh := validationSeamNeighbor ring root e he
  apply remoteFrame ring s e (site ring root k)
  · intro h
    have hs : site ring root k =
        site ring root (n - 1) := by
      calc
        site ring root k = e := h
        _ = site ring root (n - 1) := he
    have hbad := validationSiteInjective ring root
      k (n - 1) (by omega) (by omega) hs
    omega
  · intro h
    have hs : site ring root k =
        site ring root 0 := by
      calc
        site ring root k =
            ring.rightNeighbor e := h
        _ = root := hneigh
        _ = site ring root 0 := (siteZero ring root).symm
    have hbad := validationSiteInjective ring root
      k 0 (by omega) (by omega) hs
    omega

/-! S5 cannot request the root again: RUNNING excludes S0. -/

theorem validationSeamRootSer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hr : y.ser.cert = .RUNNING) :
    (serW x y).y = y.ser := by
  cases hp : x.ser.phase <;>
  cases hq : x.ser.probe <;>
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hr, hp, hq, serCanonicalC]

theorem validationSeamFSer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hr : y.ser.cert = .RUNNING)
    (hf : x.ser.phase = .F) :
    (serW x y).x = x.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hr, hf]

theorem validationSeamCOffSer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hr : y.ser.cert = .RUNNING)
    (hc : x.ser.phase = .C)
    (hoff : x.ser.wphase = .OFF) :
    (serW x y).x.phase = .C ∧
    (serW x y).x.wphase = .OFF := by
  cases hp : x.ser.probe <;>
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hr, hc, hoff, hp]

theorem validationSeamLeafOrDoneSer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = true)
    (hr : y.ser.cert = .RUNNING)
    (hc : x.ser.phase = .C)
    (hp : x.ser.probe = .PENDING ∨
      (x.ser.probe = .LEAF_OK ∧ x.ser.wphase = .OFF)) :
    (serW x y).x.phase = .C ∧
    (serW x y).x.probe = .LEAF_OK ∧
    (serW x y).x.wphase = .OFF := by
  rcases hp with hpend | hleaf
  · have h := validationSeamLeafSerializer x y
      hx hy hr hc hpend
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
  · simp [serW, serializerStep, ProjW.lift,
      hx, hy, hr, hc, hleaf.1, hleaf.2]

theorem validationSeamGhostFixed
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (he : e = site ring root (n - 1)) :
    validationGhostStep ring root s g e = g := by
  have hn := shape.width
  have hnotroot := validationSeamNotRoot ring root e hn he
  have hstart :=
    validationParentHardStartFalse ring root s g e shape hfixed
  rcases shape.stageShape with hf | hr
  · have hpb := hf.pivotBound
    have hnotparent : e ≠ site ring root g.pivot := by
      intro h
      have hs : site ring root (n - 1) =
          site ring root g.pivot := by
        calc
          site ring root (n - 1) = e := he.symm
          _ = site ring root g.pivot := h
      have hbad := validationSiteInjective ring root
        (n - 1) g.pivot (by omega) (by omega) hs
      omega
    simp [validationGhostStep, hstart,
      hf.isForward, hnotroot, hnotparent]
  · have hpb := hr.pivotBound
    by_cases hp : 1 < g.pivot
    · have hnotprev : e ≠
          site ring root (g.pivot - 1) := by
        intro h
        have hs : site ring root (n - 1) =
            site ring root (g.pivot - 1) := by
          calc
            site ring root (n - 1) = e := he.symm
            _ = site ring root (g.pivot - 1) := h
        have hbad := validationSiteInjective ring root
          (n - 1) (g.pivot - 1)
          (by omega) (by omega) hs
        omega
      simp [validationGhostStep, hstart, hnotroot,
        hr.isReturn, hp, hnotprev]
    · simp [validationGhostStep, hstart, hnotroot,
        hr.isReturn, hp]

/-- All serializer sites before n-1 are unchanged on ROOT_IN.
The only selected responder is root and S5 leaves it unchanged. -/
theorem validationSeamEarlySer
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n)
    (he : e = site ring root (n - 1))
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = true)
    (hr : (s (ring.rightNeighbor e)).ser.cert = .RUNNING) :
    ∀ k : Nat, k + 1 < n →
      ((phiW ring s e) (site ring root k)).ser =
        (s (site ring root k)).ser := by
  have hj := validationSeamNeighbor ring root e he
  have hne := rightNeighborDifferent ring (by omega) e
  have hys := validationSeamRootSer
    (s e) (s (ring.rightNeighbor e)) hx hy hr
  have hroot :
      ((phiW ring s e) root).ser = (s root).ser := by
    have hres := congrArg ProjW.ser
      (phiResponder ring s e hne)
    rw [hj] at hres hys
    exact hres.trans hys
  intro k hk
  by_cases hz : k = 0
  · simpa only [hz, siteZero] using hroot
  · have hfr := validationSeamFrame ring root s e
      hn he k hk (by omega)
    exact congrArg ProjW.ser hfr

/-- The source of a ROOT_IN seam is offset n-1. -/
theorem validationSeamLastSer
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (he : e = site ring root (n - 1)) :
    ((phiW ring s e) (site ring root (n - 1))).ser =
      (serW (s e) (s (ring.rightNeighbor e))).x :=
  congrArg ProjW.ser
    (validationParentSourceAt ring root s (n - 1) e he)

/-- When the last child is covered, its OLD pending or terminal
leaf certificate is turned into the terminal LEAF_OK form by S5. -/
theorem validationSeamPendingLeaf
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (p : Nat) (e : Fin n)
    (he : e = site ring root (n - 1))
    (hterminal : p + 2 = n)
    (hpc : pendingChild ring root s p)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = true)
    (hr : (s (ring.rightNeighbor e)).ser.cert = .RUNNING) :
    pendingChild ring root (phiW ring s e) p := by
  have hidx : p + 1 = n - 1 := by omega
  obtain ⟨hc, hp⟩ := hpc
  have hcLast :
      (s (site ring root (n - 1))).ser.phase = .C := by
    rw [←hidx]
    exact hc
  have hpLast :
      (s (site ring root (n - 1))).ser.probe =
        .PENDING ∨
      ((s (site ring root (n - 1))).ser.probe =
        .LEAF_OK ∧
       (s (site ring root (n - 1))).ser.wphase =
        .OFF) := by
    rcases hp with hpend | hinter | hleaf
    · exact Or.inl (by rw [←hidx]; exact hpend.1)
    · have hbad : False := by omega
      exact False.elim hbad
    · exact Or.inr ⟨by rw [←hidx]; exact hleaf.2.1,
        by rw [←hidx]; exact hleaf.2.2⟩
  have hcX : (s e).ser.phase = .C := by
    rw [he]
    exact hcLast
  have hpX :
      (s e).ser.probe = .PENDING ∨
      ((s e).ser.probe = .LEAF_OK ∧
       (s e).ser.wphase = .OFF) := by
    rw [he]
    exact hpLast
  have hh := validationSeamLeafOrDoneSer
    (s e) (s (ring.rightNeighbor e))
    hx hy hr hcX hpX
  have hloc := validationSeamLastSer ring root s e he
  unfold pendingChild
  rw [hidx, hloc]
  exact ⟨hh.1, Or.inr (Or.inr
    ⟨hterminal, hh.2.1, hh.2.2⟩)⟩

/-- S5 leaves all serializer data before n-1 unchanged. It may
canonicalize the last *unvisited* site, but neither the FORWARD
current parent nor its earlier completed parents are there. -/
theorem validationSeamForwardShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hn : 3 ≤ n)
    (he : e = site ring root (n - 1))
    (hf : ForwardShape ring root s g)
    (hearly : ∀ k : Nat, k + 1 < n →
      ((phiW ring s e) (site ring root k)).ser =
        (s (site ring root k)).ser)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = true)
    (hr : (s (ring.rightNeighbor e)).ser.cert = .RUNNING) :
    ForwardShape ring root (phiW ring s e) g := by
  refine {
    isForward := hf.isForward
    pivotBound := hf.pivotBound
    completed := ?_
    parentB := ?_
    parentValidating := ?_
    currentObligation := ?_
    rootFront := ?_ }
  · intro i hi
    have hlt : i.val + 1 < n := by
      have := hf.pivotBound
      omega
    unfold doneParent
    rw [hearly i.val hlt]
    exact hf.completed i hi
  · rw [hearly g.pivot hf.pivotBound]
    exact hf.parentB
  · rw [hearly g.pivot hf.pivotBound]
    exact hf.parentValidating
  · rcases hf.currentObligation with hnew | hwait
    · left
      refine ⟨hnew.1, ?_, hnew.2.2⟩
      rw [hearly g.pivot hf.pivotBound]
      exact hnew.2.1
    · right
      refine ⟨?_, hwait.2.1, ?_⟩
      · rw [hearly g.pivot hf.pivotBound]
        exact hwait.1
      · by_cases hterminal : g.pivot + 2 = n
        · exact validationSeamPendingLeaf
            ring root s g.pivot e he hterminal hwait.2.2
            hx hy hr
        · have hnext : g.pivot + 2 < n := by
            have := hf.pivotBound
            omega
          unfold pendingChild
          rw [hearly (g.pivot + 1) hnext]
          exact hwait.2.2
  · have hroot :
        ((phiW ring s e) root).ser =
          (s root).ser := by
      simpa only [siteZero] using hearly 0 (by omega)
    have hfirst :
        ((phiW ring s e) (ring.rightNeighbor root)).ser =
          (s (ring.rightNeighbor root)).ser := by
      simpa only [siteOne] using hearly 1 (by omega)
    rcases hf.rootFront with hw | hb
    · left
      rw [hroot]
      exact hw
    · right
      rw [hfirst]
      exact hb

/-- S5 preserves RETURN's leftmost F and suffix grammar.
A C/OFF at n-1 may have its probe rewritten to LEAF_OK,
which is irrelevant to the returned-suffix grammar. -/
theorem validationSeamReturnShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hr : ReturnShape ring root s g)
    (hearly : ∀ k : Nat, k + 1 < n →
      ((phiW ring s e) (site ring root k)).ser =
        (s (site ring root k)).ser)
    (hlastF :
      (s (site ring root (n - 1))).ser.phase = .F →
      ((phiW ring s e)
        (site ring root (n - 1))).ser =
          (s (site ring root (n - 1))).ser)
    (hlastC :
      (s (site ring root (n - 1))).ser.phase = .C →
      (s (site ring root (n - 1))).ser.wphase = .OFF →
      ((phiW ring s e)
        (site ring root (n - 1))).ser.phase = .C ∧
      ((phiW ring s e)
        (site ring root (n - 1))).ser.wphase = .OFF) :
    ReturnShape ring root (phiW ring s e) g := by
  have hleft :
      ((phiW ring s e) (site ring root g.pivot)).ser =
        (s (site ring root g.pivot)).ser := by
    by_cases hlast : g.pivot + 1 = n
    · have hidx : g.pivot = n - 1 := by omega
      rw [hidx]
      apply hlastF
      rw [←hidx]
      exact hr.leftmostF
    · exact hearly g.pivot (by
        have := hr.pivotBound
        omega)
  refine {
    isReturn := hr.isReturn
    covered := hr.covered
    pivotPositive := hr.pivotPositive
    pivotBound := hr.pivotBound
    completed := ?_
    leftmostF := ?_
    leftmostWphase := ?_
    suffix := ?_ }
  · intro i hi
    have hlt : i.val + 1 < n := by
      have := hr.pivotBound
      omega
    unfold doneParent
    rw [hearly i.val hlt]
    exact hr.completed i hi
  · rw [hleft]
    exact hr.leftmostF
  · rw [hleft]
    exact hr.leftmostWphase
  · intro i hi
    by_cases hlast : i.val + 1 = n
    · have hidx : i.val = n - 1 := by omega
      have hold := hr.suffix i hi
      rw [hidx] at hold ⊢
      rcases hold with hf | hc
      · left
        rw [hlastF hf.1]
        exact hf
      · right
        exact hlastC hc.1 hc.2
    · have hlt : i.val + 1 < n := by
        have := i.isLt
        omega
      rw [hearly i.val hlt]
      exact hr.suffix i hi

/-- At all covered offsets ROOT_IN preserves offSI. The root is
hardRight-scrubbed; if offset n-1 is covered, both selected SI
records were already off and I1 preserves that pair. -/
theorem validationSeamScrubbed
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (he : e = site ring root (n - 1))
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false) :
    ∀ i : Fin n, i.val < g.scrub →
      ((phiW ring s e) (site ring root i.val)).si =
        offSI c.t := by
  have hn := shape.width
  have hj := validationSeamNeighbor ring root e he
  have hne := rightNeighborDifferent ring (by omega) e
  have hv : (s (ring.rightNeighbor e)).ser.wphase =
      .VALIDATING := by
    rw [hj]
    exact shape.rootValidating
  have hrootSi :
      ((phiW ring s e) root).si = offSI c.t := by
    rw [←hj]
    exact rootSeamStep ring s e hne hv hx
  have hlastSi :
      g.scrub = n → ((phiW ring s e) e).si =
        offSI c.t := by
    intro hsc
    have hlt : n - 1 < n := by omega
    have hold := shape.scrubbed
      ⟨n - 1, hlt⟩ (by omega)
    have hsix : (s e).si = offSI c.t := by
      rw [he]
      exact hold
    have hyOld : (s (ring.rightNeighbor e)).si =
        offSI c.t := by
      rw [hj]
      have hzero := shape.scrubbed
        ⟨0, by omega⟩ (by omega)
      simpa only [siteZero] using hzero
    have hpair := twoFreeSelected
      (s e) (s (ring.rightNeighbor e)) hno hsix hyOld
    rw [phiSource]
    exact hpair.1
  intro i hi
  by_cases hz : i.val = 0
  · simpa only [hz, siteZero] using hrootSi
  · by_cases hlast : i.val = n - 1
    · have hsc : g.scrub = n := by
        have := shape.upper
        omega
      have hlastSite : site ring root i.val = e := by
        rw [hlast]
        exact he.symm
      rw [hlastSite]
      exact hlastSi hsc
    · have hlt : i.val + 1 < n := by omega
      have hfr := validationSeamFrame ring root s e
        hn he i.val hlt (by omega)
      rw [hfr]
      exact shape.scrubbed i hi

/-- Complete ROOT_IN ValidationShape lifting. -/
theorem validationRootSeamClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hclass : validationEdgeClass ring root g e =
      .rootSeam) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have he : e = site ring root (n - 1) := by
    unfold validationEdgeClass at hclass
    by_cases hs : e = site ring root (n - 1)
    · exact hs
    · rw [if_neg hs] at hclass
      by_cases hp : g.stage = .forward ∧
          e = site ring root g.pivot
      · rw [if_pos hp] at hclass
        cases hclass
      · rw [if_neg hp] at hclass
        by_cases hc : g.stage = .forward ∧
            e = site ring root (g.pivot + 1)
        · rw [if_pos hc] at hclass
          cases hclass
        · rw [if_neg hc] at hclass
          by_cases hr : ∀ i : Fin n, i.val < g.scrub →
              site ring root i.val ≠ e ∧
              site ring root i.val ≠ ring.rightNeighbor e
          · rw [if_pos hr] at hclass
            cases hclass
          · rw [if_neg hr] at hclass
            cases hclass
  have hj := validationSeamNeighbor ring root e he
  have hne := rightNeighborDifferent ring (by
    have := shape.width
    omega) e
  have hnotroot :=
    validationSeamNotRoot ring root e shape.width he
  have hx := validationPostSourceNonroot
    ring root s e hfixed hnotroot
  have hy := validationPostTargetRoot
    ring root s e hfixed hne hj
  have hr : (s (ring.rightNeighbor e)).ser.cert =
      .RUNNING := by
    rw [hj]
    exact shape.rootRunning
  have hearly := validationSeamEarlySer
    ring root s e shape.width he hx hy hr
  have hlastSer := validationSeamLastSer ring root s e he
  have hlastF :
      (s (site ring root (n - 1))).ser.phase = .F →
      ((phiW ring s e) (site ring root (n - 1))).ser =
        (s (site ring root (n - 1))).ser := by
    intro hF
    have hfX : (s e).ser.phase = .F := by
      rw [he]
      exact hF
    have hh := validationSeamFSer
      (s e) (s (ring.rightNeighbor e)) hx hy hr hfX
    rw [hlastSer, hh, he]
  have hlastC :
      (s (site ring root (n - 1))).ser.phase = .C →
      (s (site ring root (n - 1))).ser.wphase = .OFF →
      ((phiW ring s e)
        (site ring root (n - 1))).ser.phase = .C ∧
      ((phiW ring s e)
        (site ring root (n - 1))).ser.wphase = .OFF := by
    intro hC hOff
    have hcX : (s e).ser.phase = .C := by
      rw [he]
      exact hC
    have hoffX : (s e).ser.wphase = .OFF := by
      rw [he]
      exact hOff
    rw [hlastSer]
    exact validationSeamCOffSer
      (s e) (s (ring.rightNeighbor e))
      hx hy hr hcX hoffX
  have hstage :
      ForwardShape ring root (phiW ring s e) g ∨
      ReturnShape ring root (phiW ring s e) g := by
    rcases shape.stageShape with hf | hreturn
    · exact Or.inl (validationSeamForwardShape
        ring root s g e shape.width he hf hearly hx hy hr)
    · exact Or.inr (validationSeamReturnShape
        ring root s g e hreturn hearly hlastF hlastC)
  have hrootSer :
      ((phiW ring s e) root).ser = (s root).ser := by
    simpa only [siteZero] using hearly 0 (by omega)
  have hsi := validationSeamScrubbed
    ring root s g e shape he hx hno
  have hg := validationSeamGhostFixed
    ring root s g e shape hfixed he
  rw [hg]
  refine {
    genuine := shape.genuine
    protectedRoot := hfixed
    width := shape.width
    rootRunning := ?_
    rootValidating := ?_
    lower := shape.lower
    upper := shape.upper
    scrubbed := hsi
    stageShape := hstage }
  · rw [hrootSer]
    exact shape.rootRunning
  · rw [hrootSer]
    exact shape.rootValidating

/-! CoveredInside row certificates: valid independently of
the still-open global coveredInside classification theorem. -/

/-- ROOT_OUT B/DONE seeing a B child is S2R and frames both
serializer records. The RUNNING root cannot select S1 or SR. -/
theorem validationRootDoneDoneSerFrame {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hr : x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hd : x.ser.out = .DONE)
    (hc : y.ser.phase = .B) :
    (serW x y).row = "S2R" ∧
    (serW x y).x = x.ser ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hr, hb, hd, hc]

/-- Covered root (B/DONE + B) is an actual idle subrow.
The pre-existing general CoveredIdleClass supplies the lifting. -/
theorem validationCoveredRootDoneDoneClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (hno : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = false)
    (hb : (s root).ser.phase = .B)
    (hd : (s root).ser.out = .DONE)
    (hyb : (s (ring.rightNeighbor root)).ser.phase = .B) :
    ValidationShape ring root (phiW ring s root)
      (validationGhostStep ring root s g root) := by
  have hne := rightNeighborDifferent ring (by
    have := shape.width
    omega) root
  have hx := validationPostSourceRoot
    ring root s hfixed
  have hy := validationPostTargetNonroot
    ring root s root hfixed hne hne
  have hser := validationRootDoneDoneSerFrame
    (s root) (s (ring.rightNeighbor root))
    hx hy shape.rootRunning hb hd hyb
  have hstart := validationParentHardStartFalse
    ring root s g root shape hfixed
  have hghost := internalDoneDoneGhostFixed
    ring root s g root hstart hd hyb
  have hsix : (s root).si = offSI c.t := by
    have hzero := shape.scrubbed
      ⟨0, by have := shape.width; omega⟩
      (by show 0 < g.scrub; have := shape.lower; omega)
    simpa only [siteZero] using hzero
  have hsiy :
      (s (ring.rightNeighbor root)).si =
        offSI c.t := by
    have hone := shape.scrubbed
      ⟨1, by have := shape.width; omega⟩
      (by show 1 < g.scrub; have := shape.lower; omega)
    simpa only [siteOne] using hone
  have hc : CoveredIdleClass ring root s g root :=
    { oldSourceOff := hsix
      oldTargetOff := hsiy
      serializerX := hser.2.1
      serializerY := hser.2.2
      ghostFixed := hghost }
  exact validationCoveredIdleClass
    ring root s g root shape hfixed hno hc

/-- INTERNAL B/DONE + F at the left edge of a RETURN front.
The source becomes the new F/CURRENT; the old F stays F. -/
theorem validationReturnMoveSerializer {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hb : x.ser.phase = .B)
    (hd : x.ser.out = .DONE)
    (hf : y.ser.phase = .F) :
    (serW x y).row = "S2N" ∧
    (serW x y).x.phase = .F ∧
    (serW x y).x.wphase = .CURRENT ∧
    (serW x y).y = y.ser := by
  simp [serW, serializerStep, ProjW.lift,
    hx, hy, hb, hd, hf, serEnterF]

/-- The actual ghost decrements the RETURN pivot only at the
matching S2N predecessor service, and never at pivot one. -/
theorem validationReturnMoveGhost
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (hs : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardS1 = false)
    (hstage : g.stage = .returning)
    (hp : 1 < g.pivot)
    (he : e = site ring root (g.pivot - 1))
    (hb : (s e).ser.phase = .B)
    (hd : (s e).ser.out = .DONE)
    (hf : (s (ring.rightNeighbor e)).ser.phase = .F)
    (hrow : (serW (s e)
      (s (ring.rightNeighbor e))).row = "S2N") :
    validationGhostStep ring root s g e =
      { g with pivot := g.pivot - 1 } := by
  subst he
  simp [validationGhostStep, hs, hstage,
    hp, hb, hd, hf, hrow]

end EWord
end L3

namespace L3
namespace EWord

set_option autoImplicit false

/-! Offset representatives and non-seam frames. -/

theorem validationOffsetBound {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    PPL.cyclicOffset ring root e < n := by
  unfold PPL.cyclicOffset
  exact Nat.mod_lt _ ring.hn

theorem validationOffsetRepresentative {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    site ring root (PPL.cyclicOffset ring root e) = e := by
  apply Fin.ext
  change
    (root.val + ((e.val + n - root.val) % n)) % n = e.val
  by_cases hab : root.val ≤ e.val
  · have heq :
        e.val + n - root.val =
          n + (e.val - root.val) := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : e.val - root.val < n)]
    have hsum :
        root.val + (e.val - root.val) = e.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt e.isLt]
  · have hlt : e.val + n - root.val < n := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        root.val + (e.val + n - root.val) =
          e.val + n := by
      omega
    rw [hsum, Nat.add_mod_right,
      Nat.mod_eq_of_lt e.isLt]

theorem validationPositiveSiteNotRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (k : Nat) (hk : k < n) (hpos : 0 < k) :
    site ring root k ≠ root := by
  intro h
  have hs : site ring root k = site ring root 0 := by
    rw [siteZero]
    exact h
  have hbad := validationSiteInjective ring root
    k 0 hk (by omega) hs
  omega

theorem validationNonSeamOffset {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hne : e ≠ site ring root (n - 1)) :
    PPL.cyclicOffset ring root e + 1 < n := by
  have hk := validationOffsetBound ring root e
  have he := validationOffsetRepresentative ring root e
  by_cases hlt : PPL.cyclicOffset ring root e + 1 < n
  · exact hlt
  · have hlast :
        PPL.cyclicOffset ring root e = n - 1 := by
      omega
    have hbad : e = site ring root (n - 1) := by
      calc
        e = site ring root
              (PPL.cyclicOffset ring root e) := he.symm
        _ = site ring root (n - 1) := by rw [hlast]
    exact False.elim (hne hbad)

/-! The exact negative guards given by the priority classifier. -/

theorem validationCoveredClassFacts {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (g : ValidationGhost) (e : Fin n)
    (hc : validationEdgeClass ring root g e =
      .coveredInside) :
    e ≠ site ring root (n - 1) ∧
    ¬ (g.stage = .forward ∧ e = site ring root g.pivot) ∧
    ¬ (g.stage = .forward ∧
      e = site ring root (g.pivot + 1)) ∧
    ¬ (∀ i : Fin n, i.val < g.scrub →
      site ring root i.val ≠ e ∧
      site ring root i.val ≠ ring.rightNeighbor e) := by
  unfold validationEdgeClass at hc
  by_cases hs : e = site ring root (n - 1)
  · rw [if_pos hs] at hc
    cases hc
  · rw [if_neg hs] at hc
    by_cases hp : g.stage = .forward ∧
        e = site ring root g.pivot
    · rw [if_pos hp] at hc
      cases hc
    · rw [if_neg hp] at hc
      by_cases hy : g.stage = .forward ∧
          e = site ring root (g.pivot + 1)
      · rw [if_pos hy] at hc
        cases hc
      · rw [if_neg hy] at hc
        by_cases hr : ∀ i : Fin n, i.val < g.scrub →
            site ring root i.val ≠ e ∧
            site ring root i.val ≠ ring.rightNeighbor e
        · rw [if_pos hr] at hc
          cases hc
        · exact ⟨hs, hp, hy, hr⟩

/-- A coveredInside edge in FORWARD lies strictly before the
current parent, not at or beyond either frontier endpoint. -/
theorem validationForwardInsideOffset
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (hc : validationEdgeClass ring root g e =
      .coveredInside) :
    PPL.cyclicOffset ring root e < g.pivot := by
  let k := PPL.cyclicOffset ring root e
  have facts := validationCoveredClassFacts ring root g e hc
  have hbound : k + 1 < n :=
    validationNonSeamOffset ring root e facts.1
  have hk : k < n := validationOffsetBound ring root e
  have he : e = site ring root k :=
    (validationOffsetRepresentative ring root e).symm
  have hnpar := facts.2.1
  have hnchild := facts.2.2.1
  have hnremote := facts.2.2.2
  have hsc : g.scrub ≤ g.pivot + 2 := by
    rcases hf.currentObligation with hn | hw
    · omega
    · omega
  by_cases hlt : k < g.pivot
  · exact hlt
  · have hnotp : k ≠ g.pivot := by
      intro hp
      apply hnpar
      refine ⟨hf.isForward, ?_⟩
      rw [he, hp]
    have hnotc : k ≠ g.pivot + 1 := by
      intro hp
      apply hnchild
      refine ⟨hf.isForward, ?_⟩
      rw [he, hp]
    have hlarge : g.pivot + 2 ≤ k := by omega
    have hr : ∀ i : Fin n, i.val < g.scrub →
        site ring root i.val ≠ e ∧
        site ring root i.val ≠ ring.rightNeighbor e := by
      intro i hi
      have hltI : i.val < k := by omega
      have hj := validationParentNeighbor ring root k e he
      constructor
      · intro h
        have hs : site ring root i.val =
            site ring root k := by
          rw [←he]
          exact h
        have hbad := validationSiteInjective ring root
          i.val k i.isLt hk hs
        omega
      · intro h
        have hs : site ring root i.val =
            site ring root (k + 1) := by
          rw [←hj]
          exact h
        have hbad := validationSiteInjective ring root
          i.val (k + 1) i.isLt hbound hs
        omega
    exact False.elim (hnremote hr)

/-! All SI registers are off throughout RETURN and stay so on
any nonaccepting service, regardless of the selected serializer row. -/

theorem validationReturnAllSI
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hr : ReturnShape ring root s g)
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false) :
    ∀ i : Fin n,
      ((phiW ring s e) (site ring root i.val)).si =
        offSI c.t := by
  have hne := rightNeighborDifferent ring
    (by have := shape.width; omega) e
  have he := validationOffsetRepresentative ring root e
  have hk := validationOffsetBound ring root e
  have hsix : (s e).si = offSI c.t := by
    have h := shape.scrubbed ⟨PPL.cyclicOffset ring root e, hk⟩
      (by rw [hr.covered]; exact hk)
    rw [← he]
    exact h
  have hj := validationOffsetRepresentative ring root
    (ring.rightNeighbor e)
  have hjk := validationOffsetBound ring root
    (ring.rightNeighbor e)
  have hsiy : (s (ring.rightNeighbor e)).si =
      offSI c.t := by
    have h := shape.scrubbed
      ⟨PPL.cyclicOffset ring root (ring.rightNeighbor e), hjk⟩
      (by rw [hr.covered]; exact hjk)
    rw [← hj]
    exact h
  have hpair := coveredPairStep ring s e hne
    hsix hsiy hno
  intro i
  by_cases hx : site ring root i.val = e
  · rw [hx]
    exact hpair.1
  · by_cases hy : site ring root i.val =
        ring.rightNeighbor e
    · rw [hy]
      exact hpair.2
    · rw [remoteFrame ring s e (site ring root i.val) hx hy]
      exact shape.scrubbed i (by
        rw [hr.covered]
        exact i.isLt)

/-! Native-internal B/DONE + F move and its whole RETURN grammar. -/

theorem validationReturnMoveClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hr : ReturnShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hp : 1 < g.pivot)
    (he : e = site ring root (g.pivot - 1)) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hpred : g.pivot - 1 + 1 = g.pivot := by omega
  have hbound : g.pivot - 1 + 1 < n := by
    have := hr.pivotBound
    omega
  have hprev : 0 < g.pivot - 1 := by omega
  have hj : ring.rightNeighbor e = site ring root g.pivot := by
    have h := validationParentNeighbor
      ring root (g.pivot - 1) e he
    rw [hpred] at h
    exact h
  have hneq := rightNeighborDifferent ring
    (by have := shape.width; omega) e
  have hnotrootX : e ≠ root := by
    rw [he]
    exact validationPositiveSiteNotRoot ring root
      (g.pivot - 1) (by omega) hprev
  have hnotrootY : ring.rightNeighbor e ≠ root := by
    rw [hj]
    exact validationPositiveSiteNotRoot ring root
      g.pivot hr.pivotBound hr.pivotPositive
  have hpostX := validationPostSourceNonroot
    ring root s e hfixed hnotrootX
  have hpostY := validationPostTargetNonroot
    ring root s e hfixed hneq hnotrootY
  have hparent : doneParent ring root s (g.pivot - 1) :=
    hr.completed ⟨g.pivot - 1, by omega⟩ (by
      show g.pivot - 1 < g.pivot
      omega)
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hparent.1
  have hd : (s e).ser.out = .DONE := by
    rw [he]
    exact hparent.2.1
  have hf : (s (ring.rightNeighbor e)).ser.phase = .F := by
    rw [hj]
    exact hr.leftmostF
  have hrow := validationReturnMoveSerializer
    (s e) (s (ring.rightNeighbor e))
    hpostX hpostY hb hd hf
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hghost := validationReturnMoveGhost
    ring root s g e hstart hr.isReturn hp he
    hb hd hf hrow.1
  have hsrc := (validationParentSerializerAt
    ring root s (g.pivot - 1) e hneq he).1
  have hdst := (validationParentSerializerAt
    ring root s (g.pivot - 1) e hneq he).2
  have hdstOld :
      ((phiW ring s e) (site ring root g.pivot)).ser =
        (s (site ring root g.pivot)).ser := by
    have ht := hdst
    rw [hpred] at ht
    rw [ht, hrow.2.2.2, hj]
  have hroot : (phiW ring s e) root = s root := by
    have hz : 0 < n := by
      have := shape.width
      omega
    have hfr := validationParentFrame ring root s
      (g.pivot - 1) e hbound he 0 hz
      (by omega) (by omega)
    simpa only [siteZero] using hfr
  have hsi := validationReturnAllSI
    ring root s g e shape hr hno
  have hret :
      ReturnShape ring root (phiW ring s e)
        { g with pivot := g.pivot - 1 } := by
    refine {
      isReturn := ?_
      covered := ?_
      pivotPositive := ?_
      pivotBound := ?_
      completed := ?_
      leftmostF := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · dsimp
      exact hr.isReturn
    · dsimp
      exact hr.covered
    · dsimp
      omega
    · dsimp
      have := hr.pivotBound
      omega
    · intro i hi
      dsimp at hi
      have hfr := validationParentFrame ring root s
        (g.pivot - 1) e hbound he i.val i.isLt
        (by omega) (by omega)
      unfold doneParent
      rw [hfr]
      exact hr.completed i (by omega)
    · dsimp
      rw [hsrc]
      exact hrow.2.1
    · dsimp
      have hneqN : g.pivot - 1 + 1 ≠ n := by
        have := hr.pivotBound
        omega
      rw [if_neg hneqN, hsrc]
      exact hrow.2.2.1
    · intro i hi
      dsimp at hi
      by_cases his : i.val = g.pivot
      · rw [his, hdstOld]
        exact Or.inl ⟨hr.leftmostF, hr.leftmostWphase⟩
      · have hfr := validationParentFrame ring root s
          (g.pivot - 1) e hbound he i.val i.isLt
          (by omega) (by omega)
        rw [hfr]
        exact hr.suffix i (by omega)
  rw [hghost]
  refine {
    genuine := shape.genuine
    protectedRoot := hfixed
    width := shape.width
    rootRunning := ?_
    rootValidating := ?_
    lower := shape.lower
    upper := shape.upper
    scrubbed := ?_
    stageShape := Or.inr hret }
  · rw [hroot]
    exact shape.rootRunning
  · rw [hroot]
    exact shape.rootValidating
  · intro i _
    exact hsi i


/-! S3/S4: source F or C, responder F or C.  A returned
F responder may be retired to C/OFF; no source phase or
wphase is changed. The probe field is deliberately arbitrary. -/
/-- Full pointwise S3/S4 certificate, including the target
shape after an F-to-C/OFF canonicalization. -/
theorem validationReturnSuffixPairComplete {c : Compiled}
    (x y : ProjW c)
    (wp : SerWPhase)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hsx : x.ser.phase = .F ∨ x.ser.phase = .C)
    (hsy : (y.ser.phase = .F ∧ y.ser.wphase = wp) ∨
      (y.ser.phase = .C ∧ y.ser.wphase = .OFF)) :
    ((serW x y).x.phase = x.ser.phase ∧
      (serW x y).x.wphase = x.ser.wphase) ∧
    (((serW x y).y.phase = .F ∧
        (serW x y).y.wphase = wp) ∨
      ((serW x y).y.phase = .C ∧
        (serW x y).y.wphase = .OFF)) := by
  rcases hsx with hf | hc
  · rcases hsy with ⟨hyf, hwp⟩ | ⟨hyc, hwp⟩
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, hf, hyf, serCanonicalC]
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, hf, hyc, hwp]
  · rcases hsy with ⟨hyf, hwp⟩ | ⟨hyc, hwp⟩
    · cases hp : x.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hc, hyf, hp, serCanonicalC]
    · cases hp : x.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hc, hyc, hwp, hp]

/-- A non-seam S3/S4 suffix edge keeps ReturnShape unchanged.
This also handles the leftmost F as source (offset k=pivot),
and C/OFF sources with arbitrary inherited probe bytes. -/
theorem validationReturnSuffixClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n) (k : Nat)
    (shape : ValidationShape ring root s g)
    (hr : ReturnShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hk : g.pivot ≤ k)
    (hbound : k + 1 < n)
    (he : e = site ring root k) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  have hne := rightNeighborDifferent ring
    (by have := shape.width; omega) e
  have hj := validationParentNeighbor ring root k e he
  have hnotX : e ≠ root := by
    rw [he]
    exact validationPositiveSiteNotRoot ring root k
      (by omega) (by
        have := hr.pivotPositive
        omega)
  have hnotY : ring.rightNeighbor e ≠ root := by
    rw [hj]
    exact validationPositiveSiteNotRoot ring root (k + 1)
      hbound (by omega)
  have hx := validationPostSourceNonroot
    ring root s e hfixed hnotX
  have hy := validationPostTargetNonroot
    ring root s e hfixed hne hnotY
  have holdX :
      (s (site ring root k)).ser.phase = .F ∨
      (s (site ring root k)).ser.phase = .C := by
    by_cases hp : k = g.pivot
    · exact Or.inl (by rw [hp]; exact hr.leftmostF)
    · have hkgt : g.pivot < k := by omega
      rcases hr.suffix ⟨k, by omega⟩ hkgt with hf | hc
      · exact Or.inl hf.1
      · exact Or.inr hc.1
  have hsource : (s e).ser.phase = .F ∨
      (s e).ser.phase = .C := by
    rw [he]
    exact holdX
  have holdY := hr.suffix ⟨k + 1, hbound⟩ (by show g.pivot < k + 1; omega)
  have htarget :
      ((s (ring.rightNeighbor e)).ser.phase = .F ∧
       (s (ring.rightNeighbor e)).ser.wphase =
         (if k + 2 = n then .OFF else .CURRENT)) ∨
      ((s (ring.rightNeighbor e)).ser.phase = .C ∧
       (s (ring.rightNeighbor e)).ser.wphase = .OFF) := by
    rw [hj]
    exact holdY
  have hrow := validationReturnSuffixPairComplete
    (s e) (s (ring.rightNeighbor e))
    (if k + 2 = n then .OFF else .CURRENT)
    hx hy hsource htarget
  have hsrc := (validationParentSerializerAt
    ring root s k e hne he).1
  have hdst := (validationParentSerializerAt
    ring root s k e hne he).2
  have hsourceSame :
      ((phiW ring s e) (site ring root k)).ser.phase =
        (s (site ring root k)).ser.phase ∧
      ((phiW ring s e) (site ring root k)).ser.wphase =
        (s (site ring root k)).ser.wphase := by
    constructor
    · calc
        ((phiW ring s e) (site ring root k)).ser.phase =
            (serW (s e) (s (ring.rightNeighbor e))).x.phase := by
          rw [hsrc]
        _ = (s e).ser.phase := hrow.1.1
        _ = (s (site ring root k)).ser.phase := by rw [←he]
    · calc
        ((phiW ring s e) (site ring root k)).ser.wphase =
            (serW (s e) (s (ring.rightNeighbor e))).x.wphase := by
          rw [hsrc]
        _ = (s e).ser.wphase := hrow.1.2
        _ = (s (site ring root k)).ser.wphase := by rw [←he]
  have htargetGood :
      (((phiW ring s e) (site ring root (k + 1))).ser.phase =
        .F ∧
       ((phiW ring s e) (site ring root (k + 1))).ser.wphase =
        (if k + 2 = n then .OFF else .CURRENT)) ∨
      (((phiW ring s e) (site ring root (k + 1))).ser.phase =
        .C ∧
       ((phiW ring s e) (site ring root (k + 1))).ser.wphase =
        .OFF) := by
    rw [hdst]
    exact hrow.2
  have hroot : (phiW ring s e) root = s root := by
    have hfr := validationParentFrame ring root s k e
      hbound he 0 (by have := shape.width; omega)
      (by have := hr.pivotPositive; omega) (by omega)
    simpa only [siteZero] using hfr
  have hstart := validationParentHardStartFalse
    ring root s g e shape hfixed
  have hnonB : (s e).ser.phase = .C ∨
      (s e).ser.phase = .F := by
    rcases hsource with hf | hc
    · exact Or.inr hf
    · exact Or.inl hc
  have hghost := validationNonBGhostFixed
    ring root s g e hstart hnonB
  have hsi := validationReturnAllSI
    ring root s g e shape hr hno
  have hret :
      ReturnShape ring root (phiW ring s e) g := by
    refine {
      isReturn := hr.isReturn
      covered := hr.covered
      pivotPositive := hr.pivotPositive
      pivotBound := hr.pivotBound
      completed := ?_
      leftmostF := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · intro i hi
      have hfr := validationParentFrame ring root s k e
        hbound he i.val i.isLt (by omega) (by omega)
      unfold doneParent
      rw [hfr]
      exact hr.completed i hi
    · by_cases hkp : k = g.pivot
      · have h := hsourceSame.1
        rw [hkp] at h
        rw [h]
        exact hr.leftmostF
      · have hfr := validationParentFrame ring root s k e
          hbound he g.pivot hr.pivotBound
          (by omega) (by omega)
        rw [hfr]
        exact hr.leftmostF
    · by_cases hkp : k = g.pivot
      · have h := hsourceSame.2
        rw [hkp] at h
        rw [h]
        exact hr.leftmostWphase
      · have hfr := validationParentFrame ring root s k e
          hbound he g.pivot hr.pivotBound
          (by omega) (by omega)
        rw [hfr]
        exact hr.leftmostWphase
    · intro i hi
      by_cases hsrcI : i.val = k
      · have hold := hr.suffix i hi
        rw [hsrcI] at hold ⊢
        rcases hold with hf | hc
        · left
          constructor
          · rw [hsourceSame.1]
            exact hf.1
          · rw [hsourceSame.2]
            exact hf.2
        · right
          constructor
          · rw [hsourceSame.1]
            exact hc.1
          · rw [hsourceSame.2]
            exact hc.2
      · by_cases hdstI : i.val = k + 1
        · rw [hdstI]
          exact htargetGood
        · have hfr := validationParentFrame ring root s k e
            hbound he i.val i.isLt hsrcI hdstI
          rw [hfr]
          exact hr.suffix i hi
  rw [hghost]
  refine {
    genuine := shape.genuine
    protectedRoot := hfixed
    width := shape.width
    rootRunning := ?_
    rootValidating := ?_
    lower := shape.lower
    upper := shape.upper
    scrubbed := ?_
    stageShape := Or.inr hret }
  · rw [hroot]
    exact shape.rootRunning
  · rw [hroot]
    exact shape.rootValidating
  · intro i _
    exact hsi i


/-! A shared full-shape B/DONE + B idle lift: either the ROOT_OUT
S2R row or the nonroot S2N row, with real POST-E flags. -/

theorem validationCoveredDoneDoneAt
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n) (k : Nat)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (he : e = site ring root k)
    (hbound : k + 1 < n)
    (hb : (s e).ser.phase = .B)
    (hd : (s e).ser.out = .DONE)
    (hq : (s (ring.rightNeighbor e)).ser.phase = .B)
    (hsix : (s e).si = offSI c.t)
    (hsiy : (s (ring.rightNeighbor e)).si = offSI c.t) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  by_cases hr : e = root
  · rw [hr] at hfixed hno hb hd hq ⊢
    exact validationCoveredRootDoneDoneClass
      ring root s g shape hfixed hno hb hd hq
  · have hj := validationParentNeighbor ring root k e he
    have hnotY : ring.rightNeighbor e ≠ root := by
      rw [hj]
      exact validationPositiveSiteNotRoot ring root (k + 1)
        hbound (by omega)
    have hneq := rightNeighborDifferent ring
      (by have := shape.width; omega) e
    have hx := validationPostSourceNonroot
      ring root s e hfixed hr
    have hy := validationPostTargetNonroot
      ring root s e hfixed hneq hnotY
    exact validationInternalDoneDoneClass
      ring root s g e shape hfixed hno
      hx hy hb hd hq hsix hsiy

/-- FORWARD coveredInside edges have offset k < pivot and
must be B/DONE -> B idle subrows (S2N or S2R). -/
theorem validationForwardCoveredClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hf : ForwardShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hc : validationEdgeClass ring root g e =
      .coveredInside) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  let k := PPL.cyclicOffset ring root e
  have hk : k < n := validationOffsetBound ring root e
  have he : e = site ring root k :=
    (validationOffsetRepresentative ring root e).symm
  have hbound : k + 1 < n := validationNonSeamOffset
    ring root e (validationCoveredClassFacts ring root g e hc).1
  have hlt : k < g.pivot :=
    validationForwardInsideOffset ring root s g e shape hf hc
  have hj := validationParentNeighbor ring root k e he
  have hdone : doneParent ring root s k :=
    hf.completed ⟨k, hk⟩ hlt
  have hb : (s e).ser.phase = .B := by
    rw [he]
    exact hdone.1
  have hd : (s e).ser.out = .DONE := by
    rw [he]
    exact hdone.2.1
  have hq : (s (ring.rightNeighbor e)).ser.phase = .B := by
    rw [hj]
    by_cases hpar : k + 1 = g.pivot
    · rw [hpar]
      exact hf.parentB
    · have hchildlt : k + 1 < g.pivot := by omega
      exact (hf.completed ⟨k + 1, hbound⟩ hchildlt).1
  have hcov : g.pivot < g.scrub :=
    validationForwardPivotCovered ring root s g hf
  have hsix : (s e).si = offSI c.t := by
    rw [he]
    exact shape.scrubbed ⟨k, hk⟩ (by
      show k < g.scrub
      omega)
  have hsiy : (s (ring.rightNeighbor e)).si =
      offSI c.t := by
    rw [hj]
    exact shape.scrubbed ⟨k + 1, hbound⟩ (by
      show k + 1 < g.scrub
      omega)
  exact validationCoveredDoneDoneAt ring root s g e k
    shape hfixed hno he hbound hb hd hq hsix hsiy

/-! At RETURN pivot one, the root service is exactly S6/I0.
This rules out the otherwise problematic predecessor edge via
the named nonacceptance hypothesis. -/

theorem validationReturnPivotOneAccept
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (shape : ValidationShape ring root s g)
    (hr : ReturnShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s root))
    (hp : g.pivot = 1) :
    (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept =
        true := by
  have hneq := rightNeighborDifferent ring
    (by have := shape.width; omega) root
  have hpostX := validationPostSourceRoot
    ring root s hfixed
  have hpostY := validationPostTargetNonroot
    ring root s root hfixed hneq hneq
  have hdone : doneParent ring root s 0 :=
    hr.completed ⟨0, by have := shape.width; omega⟩ (by
      show 0 < g.pivot
      have := hr.pivotPositive
      omega)
  have hb : (s root).ser.phase = .B := by
    simpa only [siteZero] using hdone.1
  have hd : (s root).ser.out = .DONE := by
    simpa only [siteZero] using hdone.2.1
  have hyf :
      (s (ring.rightNeighbor root)).ser.phase = .F := by
    have hf := hr.leftmostF
    rw [hp, siteOne] at hf
    exact hf
  have hser := acceptingSerializerTerminal
    (s root) (s (ring.rightNeighbor root))
    hpostX hpostY shape.rootRunning hb hd
    shape.rootValidating hyf
  exact hser.2.1

/-- Every non-seam edge preserves the RETURN shape, excluding
the terminal root S6 by the actual hardAccept=false hypothesis. -/
theorem validationReturnNonSeamClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hr : ReturnShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hnotseam : e ≠ site ring root (n - 1)) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  let k := PPL.cyclicOffset ring root e
  have hk : k < n := validationOffsetBound ring root e
  have he : e = site ring root k :=
    (validationOffsetRepresentative ring root e).symm
  have hbound : k + 1 < n :=
    validationNonSeamOffset ring root e hnotseam
  have hj := validationParentNeighbor ring root k e he
  by_cases hearly : k + 1 < g.pivot
  · have hparent : doneParent ring root s k :=
      hr.completed ⟨k, hk⟩ (by show k < g.pivot; omega)
    have hchild : doneParent ring root s (k + 1) :=
      hr.completed ⟨k + 1, hbound⟩ hearly
    have hb : (s e).ser.phase = .B := by
      rw [he]
      exact hparent.1
    have hd : (s e).ser.out = .DONE := by
      rw [he]
      exact hparent.2.1
    have hq : (s (ring.rightNeighbor e)).ser.phase = .B := by
      rw [hj]
      exact hchild.1
    have hsix : (s e).si = offSI c.t := by
      rw [he]
      exact shape.scrubbed ⟨k, hk⟩ (by
        rw [hr.covered]
        exact hk)
    have hsiy : (s (ring.rightNeighbor e)).si =
        offSI c.t := by
      rw [hj]
      exact shape.scrubbed ⟨k + 1, hbound⟩ (by
        rw [hr.covered]
        exact hbound)
    exact validationCoveredDoneDoneAt ring root s g e k
      shape hfixed hno he hbound hb hd hq hsix hsiy
  · by_cases hmove : k + 1 = g.pivot
    · by_cases hone : g.pivot = 1
      · have hkzero : k = 0 := by omega
        have hroot : e = root := by
          rw [he, hkzero, siteZero]
        rw [hroot] at hfixed hno
        have haccept := validationReturnPivotOneAccept
          ring root s g shape hr hfixed hone
        rw [haccept] at hno
        cases hno
      · have hpositive : 1 < g.pivot := by
          have := hr.pivotPositive
          omega
        have hprev : g.pivot - 1 = k := by omega
        have hsource : e =
            site ring root (g.pivot - 1) := by
          rw [hprev]
          exact he
        exact validationReturnMoveClass
          ring root s g e shape hr hfixed hno
          hpositive hsource
    · have hge : g.pivot ≤ k := by omega
      exact validationReturnSuffixClass
        ring root s g e k shape hr hfixed hno
        hge hbound he

/-! All five edge classes are now covered by literal row
certificates and the actual ghost equations. -/

theorem validationCoveredInsideClass
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (g : ValidationGhost)
    (e : Fin n)
    (shape : ValidationShape ring root s g)
    (hfixed : WFixedRoot ring root (phiW ring s e))
    (hno : (serW (s e)
      (s (ring.rightNeighbor e))).hard.hardAccept = false)
    (hc : validationEdgeClass ring root g e =
      .coveredInside) :
    ValidationShape ring root (phiW ring s e)
      (validationGhostStep ring root s g e) := by
  rcases shape.stageShape with hf | hr
  · exact validationForwardCoveredClass
      ring root s g e shape hf hfixed hno hc
  · exact validationReturnNonSeamClass
      ring root s g e shape hr hfixed hno
      (validationCoveredClassFacts ring root g e hc).1

/-- Unconditional nonaccepting all-edge validation transport. -/
theorem validationTransport
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) :
    ValidationTransport (c := c) ring root := by
  intro s g e shape hfixed hno
  rcases validationEdgeClassCover ring root g e with
    hs | hp | hc | hu | hi
  · exact validationRootSeamClass
      ring root s g e shape hfixed hno hs
  · exact validationFrontierParentClass
      ring root s g e shape hfixed hno hp
  · exact validationChallengedChildClass
      ring root s g e shape hfixed hno hc
  · exact validationUnvisitedSuffixClass
      ring root s g e shape hfixed hno hu
  · exact validationCoveredInsideClass
      ring root s g e shape hfixed hno hi

theorem validationReachableShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    {s : Fin n → ProjW c} {g : ValidationGhost}
    (history : WValidationHistory ring root s g) :
    ValidationShape ring root s g := by
  exact validationHistorySound ring root
    (validationTransport (c := c) ring root) history

theorem validationReachableHardAcceptClean
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    {s : Fin n → ProjW c} {g : ValidationGhost}
    (history : WValidationHistory ring root s g)
    (ha : (serW (s root)
      (s (ring.rightNeighbor root))).hard.hardAccept = true) :
    ∀ i : Fin n, 0 < i.val →
      freeSI (s (site ring root i.val)).si = true := by
  exact validationHistoryHardAcceptClean ring root
    (validationTransport (c := c) ring root) history ha

end EWord
end L3
