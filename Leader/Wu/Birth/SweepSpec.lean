import Leader.Core.BalancedFailureRestart
import Leader.Core.PredictableTwoTargetFiniteTree

set_option autoImplicit false

namespace BirthSweepSpec

open FiniteUniformStoppingTree
open PredictableTwoTargetFiniteTree

/-! ## Physical sweep control -/

inductive SweepPhase where
  | idle
  | erase
  | probe
  | echo
  | commit
  deriving DecidableEq, Repr

structure Control where
  phase : SweepPhase
  color : Fin 3
  permit : Bool
  deriving DecidableEq, Repr

abbrev Config (m : Nat) := Fin m → Control
abbrev Edge (m : Nat) := Fin m

def nextSite {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

def nextColor (c : Fin 3) : Fin 3 :=
  ⟨(c.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

def setAt {m : Nat} (x : Config m) (i : Fin m) (q : Control) :
    Config m :=
  fun j => if j = i then q else x j

@[simp] theorem setAt_eq {m : Nat} (x : Config m) (i : Fin m)
    (q : Control) :
    setAt x i q i = q := by
  unfold setAt
  rw [if_pos rfl]

theorem setAt_ne {m : Nat} (x : Config m) (i j : Fin m)
    (q : Control) (h : j ≠ i) :
    setAt x i q j = x j := by
  unfold setAt
  rw [if_neg h]

/-- Physical inputs supplied by the host protocol.  None is a proof ghost.
`secondBirth` is deliberately separate from the barrier/sweep path. -/
structure SweepModel (m : Nat) where
  leaderAt : Fin m → Bool
  resetAt : Fin m → Bool
  aligned : Config m → Bool
  secondBirth : Config m → Fin m → Bool

def Leaderless {m : Nat} (M : SweepModel m) : Prop :=
  ∀ i, M.leaderAt i = false

/-- Bool-valued operational leader contact. -/
def leaderContactGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Bool :=
  M.leaderAt e || M.leaderAt (nextSite hm e)

/-- Prop projection used only in specifications. -/
def leaderContact {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Prop :=
  leaderContactGuard M hm e = true

/-- Bool-valued operational reset contact. -/
def resetContactGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Bool :=
  M.resetAt e || M.resetAt (nextSite hm e)

/-- Prop projection used only in specifications. -/
def resetContact {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Prop :=
  resetContactGuard M hm e = true

/-- Highest-priority invalidation guard. -/
def invalidateGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Bool :=
  leaderContactGuard M hm e || resetContactGuard M hm e

/-- Prop projection of the invalidation guard. -/
def invalidateEvent {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (e : Fin m) : Prop :=
  invalidateGuard M hm e = true

/-- Commit guard, now explicitly Bool-valued. -/
def commitGuard {m : Nat} (x : Config m) (e : Fin m) : Bool :=
  decide ((x e).phase = .commit ∧ (x e).permit = true)

/-- Launch guard, now explicitly Bool-valued. -/
def launchGuard {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Bool :=
  decide ((x e).phase = .idle ∧
    (x e).permit = true ∧
    (x (nextSite hm e)).phase = .idle)

/-- Commit is genuine only after invalidation priority is accounted for. -/
def commitEventGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Bool :=
  (! invalidateGuard M hm e) && commitGuard x e

/-- Launch is genuine only after invalidation and commit priority are accounted
for. -/
def launchEventGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Bool :=
  (! invalidateGuard M hm e) && (! commitGuard x e) && launchGuard hm x e

def CommitEvent {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Prop :=
  commitEventGuard M hm x e = true

def LaunchEvent {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Prop :=
  launchEventGuard M hm x e = true

theorem commitEvent_parts
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (h : CommitEvent M hm x e) :
    invalidateGuard M hm e = false ∧ commitGuard x e = true := by
  unfold CommitEvent commitEventGuard at h
  cases hi : invalidateGuard M hm e <;>
    cases hc : commitGuard x e <;>
    simp_all

theorem launchEvent_parts
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (h : LaunchEvent M hm x e) :
    invalidateGuard M hm e = false ∧
      commitGuard x e = false ∧
      launchGuard hm x e = true := by
  unfold LaunchEvent launchEventGuard at h
  cases hi : invalidateGuard M hm e <;>
    cases hc : commitGuard x e <;>
    cases hl : launchGuard hm x e <;>
    simp_all

theorem commitEvent_of_parts
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = false)
    (hcommit : commitGuard x e = true) :
    CommitEvent M hm x e := by
  unfold CommitEvent commitEventGuard
  rw [hinvalid, hcommit]
  rfl

theorem launchEvent_of_parts
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = false)
    (hcommit : commitGuard x e = false)
    (hlaunch : launchGuard hm x e = true) :
    LaunchEvent M hm x e := by
  unfold LaunchEvent launchEventGuard
  rw [hinvalid, hcommit, hlaunch]
  rfl

def idleControl (c : Fin 3) : Control :=
  { phase := .idle, color := c, permit := false }

def eraseControl (c : Fin 3) : Control :=
  { phase := .erase, color := c, permit := false }

def probeControl (c : Fin 3) : Control :=
  { phase := .probe, color := c, permit := false }

def echoControl (c : Fin 3) : Control :=
  { phase := .echo, color := c, permit := false }

def commitControl (c : Fin 3) : Control :=
  { phase := .commit, color := c, permit := true }

/-- Raw launch with an explicitly chosen reuse color. -/
def launchRaw {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) (c : Fin 3) : Config m :=
  let r := nextSite hm e
  setAt (setAt x e (eraseControl c)) r (probeControl c)

/-- The physical launch advances the constant palette and clears permission on
its two written cells. -/
def launchStep {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Config m :=
  launchRaw hm x e (nextColor (x e).color)

/-- A leader/reset contact kills the local sweep footprint and permission. -/
def invalidateStep {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Config m :=
  let r := nextSite hm e
  setAt (setAt x e (idleControl (x e).color))
    r (idleControl (x r).color)

/-- Commit consumes permission.  The host birth write is represented by the
stopped success event below rather than by adding a leader bit to `Control`. -/
def commitStep {m : Nat} (x : Config m) (e : Fin m) : Config m :=
  setAt x e (idleControl (x e).color)

/-- Service subguards are Bool-valued too, so no dependent-if branch needs an
extra Decidable instance. -/
def moveGuard (left right : Control) : Bool :=
  decide (left.phase = .probe ∧ right.phase = .idle)

def closeGuard (left right : Control) : Bool :=
  decide (left.phase = .probe ∧
    right.phase = .erase ∧
    left.color = right.color)

def echoGuard (left : Control) : Bool :=
  decide (left.phase = .echo)

/-- The three service subclauses form one physical service clause. -/
def serviceStep {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Config m :=
  let r := nextSite hm e
  let left := x e
  let right := x r
  if moveGuard left right = true then
    setAt (setAt x e (idleControl left.color)) r (probeControl left.color)
  else if closeGuard left right = true then
    setAt (setAt x e (idleControl left.color)) r (echoControl left.color)
  else if echoGuard left = true then
    setAt x e (commitControl left.color)
  else
    x

/-- One total physical transition with exactly four top-level clauses. -/
def sweepStep {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Config m :=
  if invalidateGuard M hm e = true then
    invalidateStep hm x e
  else if commitGuard x e = true then
    commitStep x e
  else if launchGuard hm x e = true then
    launchStep hm x e
  else
    serviceStep hm x e

theorem sweepStep_invalidate
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = true) :
    sweepStep M hm x e = invalidateStep hm x e := by
  simp [sweepStep, hinvalid]

theorem sweepStep_commit
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = false)
    (hcommit : commitGuard x e = true) :
    sweepStep M hm x e = commitStep x e := by
  simp [sweepStep, hinvalid, hcommit]

theorem sweepStep_launch
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = false)
    (hcommit : commitGuard x e = false)
    (hlaunch : launchGuard hm x e = true) :
    sweepStep M hm x e = launchStep hm x e := by
  simp [sweepStep, hinvalid, hcommit, hlaunch]

theorem sweepStep_service
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hinvalid : invalidateGuard M hm e = false)
    (hcommit : commitGuard x e = false)
    (hlaunch : launchGuard hm x e = false) :
    sweepStep M hm x e = serviceStep hm x e := by
  simp [sweepStep, hinvalid, hcommit, hlaunch]

theorem commit_consumes_permission
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (h : CommitEvent M hm x e) :
    (sweepStep M hm x e e).permit = false := by
  obtain ⟨hinvalid, hcommit⟩ := commitEvent_parts M hm x e h
  rw [sweepStep_commit M hm x e hinvalid hcommit]
  unfold commitStep
  calc
    (setAt x e (idleControl (x e).color) e).permit =
        (idleControl (x e).color).permit :=
      congrArg Control.permit (setAt_eq x e (idleControl (x e).color))
    _ = false := rfl

/-!
For `launch_clears_permission` I keep the original hypothesis `0 < m`, hence
also the one-site ring.  In the aliasing branch `e = nextSite hm e`, the outer
write in `launchRaw` is the final write and is `probeControl`; its permission is
already false.  Thus no `1 < m` hypothesis and no modular-arithmetic
contradiction are needed.
-/
theorem launch_clears_permission
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (h : LaunchEvent M hm x e) :
    (sweepStep M hm x e e).permit = false ∧
      (sweepStep M hm x e (nextSite hm e)).permit = false := by
  obtain ⟨hinvalid, hcommit, hlaunch⟩ := launchEvent_parts M hm x e h
  rw [sweepStep_launch M hm x e hinvalid hcommit hlaunch]
  have setAt_of_eq (y : Config m) (i j : Fin m) (q : Control)
      (hji : j = i) : setAt y i q j = q := by
    calc
      setAt y i q j = setAt y i q i := congrArg (setAt y i q) hji
      _ = q := setAt_eq y i q
  unfold launchStep launchRaw
  constructor
  · by_cases hloop : e = nextSite hm e
    · calc
        (setAt
            (setAt x e (eraseControl (nextColor (x e).color)))
            (nextSite hm e)
            (probeControl (nextColor (x e).color)) e).permit =
            (probeControl (nextColor (x e).color)).permit := by
          rw [setAt_of_eq _ _ _ _ hloop]
        _ = false := rfl
    · calc
        (setAt
            (setAt x e (eraseControl (nextColor (x e).color)))
            (nextSite hm e)
            (probeControl (nextColor (x e).color)) e).permit =
            (setAt x e (eraseControl (nextColor (x e).color)) e).permit := by
          rw [setAt_ne _ _ _ _ hloop]
        _ = (eraseControl (nextColor (x e).color)).permit := by
          rw [setAt_eq]
        _ = false := rfl
  · calc
      (setAt
          (setAt x e (eraseControl (nextColor (x e).color)))
          (nextSite hm e)
          (probeControl (nextColor (x e).color)) (nextSite hm e)).permit =
          (probeControl (nextColor (x e).color)).permit := by
        rw [setAt_eq]
      _ = false := rfl

/-! ## Separate proof-only ghost -/

structure Ghost (m : Nat) where
  visited : Fin m → Bool
  ancestry : Fin m → Option (Fin m)
  sawLeader : Bool
  root : Option (Fin m)

structure TaggedConfig (m : Nat) where
  concrete : Config m
  ghost : Ghost m

def forget {m : Nat} (t : TaggedConfig m) : Config m :=
  t.concrete

def emptyGhost {m : Nat} (sawLeader : Bool) : Ghost m :=
  { visited := fun _ => false
    ancestry := fun _ => none
    sawLeader := sawLeader
    root := none }

/-- A launch resets proof history.  Both launch cells descend from one root. -/
def launchGhost {m : Nat} (hm : 0 < m) (e : Fin m) : Ghost m :=
  let r := nextSite hm e
  { visited := fun i =>
      if i = e ∨ i = r then true else false
    ancestry := fun i =>
      if i = e ∨ i = r then some e else none
    sawLeader := false
    root := some e }

def markGhost {m : Nat} (g : Ghost m) (root site : Fin m) : Ghost m :=
  { visited := fun i => if i = site then true else g.visited i
    ancestry := fun i => if i = site then some root else g.ancestry i
    sawLeader := g.sawLeader
    root := some root }

/-- Bool guard for the only service that may enlarge the ghost prefix. -/
def frontierGuard {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Bool :=
  let r := nextSite hm e
  moveGuard (x e) (x r) || closeGuard (x e) (x r)

/-- Prop projection retained for specification statements. -/
def FrontierService {m : Nat} (hm : 0 < m) (x : Config m)
    (e : Fin m) : Prop :=
  frontierGuard hm x e = true

def serviceGhost {m : Nat} (hm : 0 < m) (x : Config m)
    (g : Ghost m) (e : Fin m) : Ghost m :=
  if frontierGuard hm x e = true then
    match g.root with
    | none => g
    | some root => markGhost g root (nextSite hm e)
  else
    g

/-- Ghost update follows physical branch selection but never influences it. -/
def ghostStep {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (g : Ghost m) (e : Fin m) : Ghost m :=
  if invalidateGuard M hm e = true then
    emptyGhost
      (if leaderContactGuard M hm e = true then true else g.sawLeader)
  else if commitGuard x e = true then
    emptyGhost g.sawLeader
  else if launchGuard hm x e = true then
    launchGhost hm e
  else
    serviceGhost hm x g e

def taggedStep {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (t : TaggedConfig m) (e : Fin m) : TaggedConfig m :=
  { concrete := sweepStep M hm t.concrete e
    ghost := ghostStep M hm t.concrete t.ghost e }

@[simp] theorem forget_taggedStep
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (t : TaggedConfig m) (e : Fin m) :
    forget (taggedStep M hm t e) = sweepStep M hm (forget t) e := by
  rfl

/-! ## Provenance induction -/

def PrefixProvenance {m : Nat} (root : Fin m) (g : Ghost m) : Prop :=
  ∀ i, g.visited i = true → g.ancestry i = some root

def NoVisited {m : Nat} (g : Ghost m) : Prop :=
  ∀ i, g.visited i = false

/-- A lineage is either live for one launch root or completely cleared. -/
def Lineage {m : Nat} (root : Fin m) (g : Ghost m) : Prop :=
  (g.root = some root ∧ PrefixProvenance root g) ∨
    (g.root = none ∧ NoVisited g)

theorem emptyGhost_lineage
    {m : Nat} (root : Fin m) (saw : Bool) :
    Lineage root (emptyGhost saw) := by
  right
  exact ⟨rfl, fun _ => rfl⟩

theorem launchGhost_lineage
    {m : Nat} (hm : 0 < m) (e : Fin m) :
    Lineage e (launchGhost hm e) := by
  left
  constructor
  · rfl
  · intro i hi
    by_cases h : i = e ∨ i = nextSite hm e
    · simp [launchGhost, h]
    · simp [launchGhost, h] at hi

theorem markGhost_lineage
    {m : Nat} (root : Fin m) (g : Ghost m) (site : Fin m)
    (hprov : PrefixProvenance root g) :
    Lineage root (markGhost g root site) := by
  left
  constructor
  · rfl
  · intro i hi
    by_cases hsite : i = site
    · simp [markGhost, hsite]
    · have hold : g.visited i = true := by
        simpa [markGhost, hsite] using hi
      have ha := hprov i hold
      simpa [markGhost, hsite] using ha

theorem serviceGhost_lineage
    {m : Nat} (hm : 0 < m) (x : Config m) (g : Ghost m)
    (e root : Fin m) (hlin : Lineage root g) :
    Lineage root (serviceGhost hm x g e) := by
  cases hfront : frontierGuard hm x e with
  | false =>
      simpa [serviceGhost, hfront] using hlin
  | true =>
      rcases hlin with hcur | hclear
      · rcases hcur with ⟨hroot, hprov⟩
        have hmarked :=
          markGhost_lineage root g (nextSite hm e) hprov
        simpa [serviceGhost, hfront, hroot] using hmarked
      · rcases hclear with ⟨hroot, hnone⟩
        have heq : serviceGhost hm x g e = g := by
          simp [serviceGhost, hfront, hroot]
        rw [heq]
        exact Or.inr ⟨hroot, hnone⟩

theorem ghostStep_preserves_lineage
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (g : Ghost m) (e root : Fin m)
    (hlin : Lineage root g)
    (hnolaunch : ¬ LaunchEvent M hm x e) :
    Lineage root (ghostStep M hm x g e) := by
  cases hinvalid : invalidateGuard M hm e with
  | true =>
      simpa [ghostStep, hinvalid] using
        (emptyGhost_lineage root
          (if leaderContactGuard M hm e = true then true else g.sawLeader))
  | false =>
      cases hcommit : commitGuard x e with
      | true =>
          simpa [ghostStep, hinvalid, hcommit] using
            (emptyGhost_lineage root g.sawLeader)
      | false =>
          cases hlaunch : launchGuard hm x e with
          | true =>
              exact False.elim
                (hnolaunch
                  (launchEvent_of_parts M hm x e hinvalid hcommit hlaunch))
          | false =>
              simpa [ghostStep, hinvalid, hcommit, hlaunch] using
                serviceGhost_lineage hm x g e root hlin

theorem taggedStep_launch_lineage
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (t : TaggedConfig m) (e : Fin m)
    (hlaunch : LaunchEvent M hm (forget t) e) :
    Lineage e (taggedStep M hm t e).ghost := by
  obtain ⟨hinvalid, hcommit, hguard⟩ :=
    launchEvent_parts M hm (forget t) e hlaunch
  have hnc : commitGuard t.concrete e = false := hcommit
  have hgl : launchGuard hm t.concrete e = true := hguard
  show Lineage e (ghostStep M hm t.concrete t.ghost e)
  simp only [ghostStep, hinvalid, hnc, hgl]
  exact launchGhost_lineage hm e

theorem taggedStep_preserves_lineage
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (t : TaggedConfig m) (e root : Fin m)
    (hlin : Lineage root t.ghost)
    (hnolaunch : ¬ LaunchEvent M hm (forget t) e) :
    Lineage root (taggedStep M hm t e).ghost := by
  exact ghostStep_preserves_lineage M hm t.concrete t.ghost e root
    hlin hnolaunch

def runTagged {m : Nat} (M : SweepModel m) (hm : 0 < m) :
    TaggedConfig m → List (Fin m) → TaggedConfig m
  | t, [] => t
  | t, e :: rest => runTagged M hm (taggedStep M hm t e) rest

def NoRelaunchAlong {m : Nat} (M : SweepModel m) (hm : 0 < m) :
    TaggedConfig m → List (Fin m) → Prop
  | _, [] => True
  | t, e :: rest =>
      ¬ LaunchEvent M hm (forget t) e ∧
        NoRelaunchAlong M hm (taggedStep M hm t e) rest

theorem runTagged_preserves_lineage
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (root : Fin m) (t : TaggedConfig m) (word : List (Fin m))
    (hnorelaunch : NoRelaunchAlong M hm t word)
    (hlin : Lineage root t.ghost) :
    Lineage root (runTagged M hm t word).ghost := by
  induction word generalizing t with
  | nil =>
      exact hlin
  | cons e rest ih =>
      rcases hnorelaunch with ⟨hnolaunch, htail⟩
      exact ih (taggedStep M hm t e) htail
        (taggedStep_preserves_lineage M hm t e root hlin hnolaunch)

theorem Lineage.prefix
    {m : Nat} {root : Fin m} {g : Ghost m}
    (hlin : Lineage root g) : PrefixProvenance root g := by
  rcases hlin with hcur | hclear
  · exact hcur.2
  · intro i hi
    have hz := hclear.2 i
    rw [hz] at hi
    cases hi

/-- Post-launch interactions preserve launch-root provenance as long as there
is no second launch.  The length equality records the service count. -/
theorem erase_prefix_provenance
    {m k : Nat} (M : SweepModel m) (hm : 0 < m)
    (t : TaggedConfig m) (launchEdge : Fin m)
    (word : List (Fin m)) (_hk : word.length = k)
    (hlaunch : LaunchEvent M hm (forget t) launchEdge)
    (hnorelaunch :
      NoRelaunchAlong M hm (taggedStep M hm t launchEdge) word) :
    PrefixProvenance launchEdge
      (runTagged M hm (taggedStep M hm t launchEdge) word).ghost := by
  have hstart := taggedStep_launch_lineage M hm t launchEdge hlaunch
  have hend := runTagged_preserves_lineage M hm launchEdge
    (taggedStep M hm t launchEdge) word hnorelaunch hstart
  exact hend.prefix

/-! ## Fixed-palette forged-certificate defense -/

/-- All same-color evidence is physically neutral before that color is reused. -/
def ScrubbedColor {m : Nat} (x : Config m) (c : Fin 3) : Prop :=
  ∀ i, (x i).color = c →
    (x i).phase = .idle ∧ (x i).permit = false

/-- Evidence is eligible if it is active or has a permission bit. -/
def EligibleColor {m : Nat} (x : Config m) (c : Fin 3)
    (i : Fin m) : Prop :=
  (x i).color = c ∧
    ((x i).phase ≠ .idle ∨ (x i).permit = true)

/-- Scrub-before-reuse: after one color is globally neutral, reusing it can
create eligible same-color evidence only on the two newly written cells. -/
theorem scrub_before_reuse
    {m : Nat} (hm : 0 < m) (x : Config m)
    (root i : Fin m) (c : Fin 3)
    (hscrub : ScrubbedColor x c)
    (heligible : EligibleColor (launchRaw hm x root c) c i) :
    i = root ∨ i = nextSite hm root := by
  by_cases hright : i = nextSite hm root
  · exact Or.inr hright
  · by_cases hleft : i = root
    · exact Or.inl hleft
    · have hstay : launchRaw hm x root c i = x i := by
        change
          setAt (setAt x root (eraseControl c))
            (nextSite hm root) (probeControl c) i = x i
        calc
          setAt (setAt x root (eraseControl c))
              (nextSite hm root) (probeControl c) i =
              setAt x root (eraseControl c) i :=
            setAt_ne _ _ _ _ hright
          _ = x i := setAt_ne _ _ _ _ hleft
      change
        (launchRaw hm x root c i).color = c ∧
          ((launchRaw hm x root c i).phase ≠ .idle ∨
            (launchRaw hm x root c i).permit = true) at heligible
      rw [hstay] at heligible
      have hneutral := hscrub i heligible.1
      rcases heligible.2 with hphase | hpermit
      · exact False.elim (hphase hneutral.1)
      · rw [hneutral.2] at hpermit
        cases hpermit

/-!
Colour-reuse verdict.  `scrub_before_reuse_three` is the exact positive
three-colour defence in this file: if the colour selected by `nextColor` is
`ScrubbedColor` immediately before reuse, every eligible witness of that colour
after launch is one of the two cells just written by that launch.  Thus three
colours are sufficient under that scrub invariant.

The scrub premise is substantive: `three_colors_without_scrub_collision` below
shows that `Fin 3` by itself is not safe from arbitrary physical state.  The
same arbitrary-initialisation collision exists for every fixed finite palette;
a larger fixed palette number does not remove it.  What is required is the
scrub-before-reuse invariant, not a fourth colour.
-/
/-- The actual three-color policy is safe whenever the color selected for
reuse has first been scrubbed. -/
theorem scrub_before_reuse_three
    {m : Nat} (hm : 0 < m) (x : Config m)
    (root i : Fin m)
    (hscrub : ScrubbedColor x (nextColor (x root).color))
    (heligible :
      EligibleColor (launchStep hm x root)
        (nextColor (x root).color) i) :
    i = root ∨ i = nextSite hm root := by
  apply scrub_before_reuse hm x root i (nextColor (x root).color) hscrub
  simpa [launchStep] using heligible

/-- Arbitrary initialization can forge one committable witness of every one of
the three colors at once.  Thus palette size alone is not the defense.  The
same construction scales to every fixed finite palette: no larger fixed number
removes the arbitrary-initialization collision.  With an actual global scrub,
even one reusable color is logically sufficient for this serialized skeleton;
therefore three colors are sufficient under `ScrubbedColor`. -/
def forgedPalette : Config 3 :=
  fun i =>
    { phase := .commit
      color := i
      permit := true }

theorem three_colors_without_scrub_collision (c : Fin 3) :
    EligibleColor forgedPalette c c ∧
      (forgedPalette c).phase = .commit ∧
      (forgedPalette c).permit = true := by
  simp [EligibleColor, forgedPalette]

/-! ## Commit soundness residual and deterministic renewal core -/

def FullTraversal {m : Nat} (g : Ghost m) : Prop :=
  ∀ i, g.visited i = true

/-- Combined sweep/second-path birth guard. -/
def birthGuard {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Bool :=
  commitEventGuard M hm x e || M.secondBirth x e

def BirthEvent {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : Prop :=
  birthGuard M hm x e = true

theorem birthEvent_of_commit
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (hcommit : CommitEvent M hm x e) :
    BirthEvent M hm x e := by
  unfold BirthEvent birthGuard
  unfold CommitEvent at hcommit
  rw [hcommit]
  rfl

theorem birthEvent_of_secondBirth
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hsecond : M.secondBirth x e = true) :
    BirthEvent M hm x e := by
  unfold BirthEvent birthGuard
  simp [hsecond]

/-- Stopped interface used by the finite renewal machinery.  The isolated
birth attempt has no failure transition. -/
def birthStep {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) : StopNode (Config m) :=
  if birthGuard M hm x e = true then
    .success
  else
    .active (sweepStep M hm x e)

theorem birthStep_success
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (hbirth : BirthEvent M hm x e) :
    birthStep M hm x e = .success := by
  unfold BirthEvent at hbirth
  simp [birthStep, hbirth]

theorem birthStep_active
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m) (hbirth : ¬ BirthEvent M hm x e) :
    birthStep M hm x e = .active (sweepStep M hm x e) := by
  have hguard : birthGuard M hm x e = false := by
    cases hcase : birthGuard M hm x e with
    | false => rfl
    | true =>
        exact False.elim (hbirth hcase)
  simp [birthStep, hguard]

/-- `washed` is the caller's concrete/ghost wash invariant.  `rank`, `target`,
and `bound` are proof data, not protocol fields.  The aligned branch requires
the second birth path.  Hence an aligned probe-free barrier fixed point with
`secondBirth = false` cannot instantiate this residual. -/
structure BirthResidual
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (washed : TaggedConfig m → Prop)
    (rank : Config m → Nat)
    (target : Config m → Fin m)
    (bound : Nat) where
  commitSound :
    ∀ t e, washed t → CommitEvent M hm (forget t) e →
      FullTraversal t.ghost ∧ Leaderless M
  renewalCore :
    Leaderless M →
    ∀ x,
      rank x < bound ∧
      (((M.aligned x = true ∧
          M.secondBirth x (target x) = true) ∨
        (M.aligned x = false ∧
          (BirthEvent M hm x (target x) ∨
            rank (sweepStep M hm x (target x)) < rank x)))) ∧
      (∀ e, ¬ BirthEvent M hm x e →
        rank (sweepStep M hm x e) ≤ rank x)

/-- Physical commit soundness remains one explicit residual field. -/
theorem commit_sound_after_wash
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    {t : TaggedConfig m} {e : Fin m}
    (hwash : washed t) (hcommit : CommitEvent M hm (forget t) e) :
    FullTraversal t.ghost ∧ Leaderless M :=
  R.commitSound t e hwash hcommit

theorem persistent_leader_blocks_commit
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    {t : TaggedConfig m} {e i : Fin m}
    (hwash : washed t) (hleader : M.leaderAt i = true) :
    ¬ CommitEvent M hm (forget t) e := by
  intro hcommit
  have hsound := commit_sound_after_wash R hwash hcommit
  have hfalse := hsound.2 i
  rw [hleader] at hfalse
  cases hfalse

theorem leaderless_aligned_second_birth
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (x : Config m)
    (haligned : M.aligned x = true) :
    M.secondBirth x (target x) = true := by
  have hcore := (R.renewalCore hleaderless x).2.1
  rcases hcore with halign | hnonalign
  · exact halign.2
  · have hfalse := hnonalign.1
    rw [haligned] at hfalse
    cases hfalse

theorem leaderless_nonAligned_rank_progress
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (x : Config m)
    (hnonaligned : M.aligned x = false) :
    BirthEvent M hm x (target x) ∨
      rank (sweepStep M hm x (target x)) < rank x := by
  have hcore := (R.renewalCore hleaderless x).2.1
  rcases hcore with halign | hnonalign
  · have hfalse := halign.1
    rw [hnonaligned] at hfalse
    cases hfalse
  · exact hnonalign.2

theorem renewal_target_progress
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (x : Config m) :
    BirthEvent M hm x (target x) ∨
      rank (sweepStep M hm x (target x)) < rank x := by
  have hcore := (R.renewalCore hleaderless x).2.1
  rcases hcore with halign | hnonalign
  · left
    exact birthEvent_of_secondBirth M hm x (target x) halign.2
  · exact hnonalign.2

theorem renewal_rank_nonincrease
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (x : Config m) (e : Fin m)
    (hnoBirth : ¬ BirthEvent M hm x e) :
    rank (sweepStep M hm x e) ≤ rank x :=
  (R.renewalCore hleaderless x).2.2 e hnoBirth

theorem renewal_rank_lt_bound
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (x : Config m) :
    rank x < bound :=
  (R.renewalCore hleaderless x).1

/-! ## Deterministic rank to exact state-uniform success mass -/

def renewalPotential {m : Nat} (rank : Config m → Nat) :
    StopNode (Config m) → Nat
  | .success => 0
  | .failure => 0
  | .active x => m * (rank x + 1)

theorem mul_eq_self_add_pred_mul
    (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [Nat.succ_mul, Nat.add_comm]

/-- One proof-selected progress edge and nonincrease on every other non-birth
edge give a Bellman supersolution of expected cost at most `m*(rank+1)`. -/
theorem renewalPotential_super
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) :
    NatBellmanSuperSolution (birthStep M hm) 1
      (renewalPotential rank) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  let a := target x
  let C := m * (rank x + 1)
  let g : Fin m → Nat :=
    fun e => if e = a then m * rank x else C
  have hpoint : ∀ e : Fin m,
      renewalPotential rank (birthStep M hm x e) ≤ g e := by
    intro e
    by_cases hbirth : BirthEvent M hm x e
    · rw [birthStep_success M hm x e hbirth]
      change 0 ≤ g e
      exact Nat.zero_le _
    · have hnon := renewal_rank_nonincrease R hleaderless x e hbirth
      rw [birthStep_active M hm x e hbirth]
      change m * (rank (sweepStep M hm x e) + 1) ≤ g e
      by_cases hea : e = a
      · subst e
        have hprogress :
            BirthEvent M hm x a ∨
              rank (sweepStep M hm x a) < rank x := by
          simpa [a] using renewal_target_progress R hleaderless x
        rcases hprogress with hnow | hdrop
        · exact False.elim (hbirth hnow)
        · have hs :
              rank (sweepStep M hm x a) + 1 ≤ rank x := by
            omega
          rw [show g a = m * rank x by simp [g]]
          exact Nat.mul_le_mul_left m hs
      · rw [show g e = C by simp [g, hea]]
        exact Nat.mul_le_mul_left m (Nat.succ_le_succ hnon)
  have hsum :
      (List.ofFn (fun e : Fin m =>
        renewalPotential rank (birthStep M hm x e))).sum ≤
        (List.ofFn g).sum :=
    ofFn_sum_le _ _ hpoint
  have hgsum :
      (List.ofFn g).sum = g a + (m - 1) * C :=
    ofFn_sum_one_value_else_const a g C (by
      intro e hne
      simp [g, hne])
  have hga : g a = m * rank x := by
    simp [g]
  have hC : C = m * rank x + m := by
    change m * (rank x + 1) = m * rank x + m
    rw [Nat.mul_add, Nat.mul_one]
  change
    1 * m +
      (List.ofFn (fun e : Fin m =>
        renewalPotential rank (birthStep M hm x e))).sum ≤
      m * (m * (rank x + 1))
  rw [Nat.one_mul]
  calc
    m + (List.ofFn (fun e : Fin m =>
        renewalPotential rank (birthStep M hm x e))).sum ≤
        m + (List.ofFn g).sum := Nat.add_le_add_left hsum m
    _ = m + (m * rank x + (m - 1) * C) := by
      rw [hgsum, hga]
    _ = C + (m - 1) * C := by
      rw [hC]
      ac_rfl
    _ = m * C := (mul_eq_self_add_pred_mul m C hm).symm
    _ = m * (m * (rank x + 1)) := by
      rfl

def renewalBudget (m bound : Nat) : Nat := m * bound

def renewalHorizon (m bound : Nat) : Nat :=
  2 * renewalBudget m bound

theorem birthStep_ne_failure
    {m : Nat} (M : SweepModel m) (hm : 0 < m) :
    ∀ x e, birthStep M hm x e ≠ .failure := by
  intro x e
  cases hguard : birthGuard M hm x e <;>
    simp [birthStep, hguard]

/-- Fixed-horizon every-active-state renewal mass.  The constant is two and
`H = 2*m*bound`.  The theorem is unavailable on an aligned barrier-only fixed
point unless the model supplies the second birth path required by
`BirthResidual.renewalCore`. -/
theorem leaderless_service_renewal_mass
    {m : Nat} {M : SweepModel m} {hm : 0 < m}
    {washed : TaggedConfig m → Prop}
    {rank : Config m → Nat} {target : Config m → Fin m}
    {bound : Nat}
    (R : BirthResidual M hm washed rank target bound)
    (hleaderless : Leaderless M) (hbound : 0 < bound) :
    ∀ x,
      m ^ renewalHorizon m bound ≤
        2 * successCount (birthStep M hm) (.active x)
          (renewalHorizon m bound) := by
  intro x
  let B := renewalBudget m bound
  let H := renewalHorizon m bound
  have hsuper := renewalPotential_super R hleaderless
  have hrank := renewal_rank_lt_bound R hleaderless x
  have hsucc : rank x + 1 ≤ bound := by
    omega
  have hpotential :
      renewalPotential rank (.active x) ≤ B := by
    change m * (rank x + 1) ≤ m * bound
    exact Nat.mul_le_mul_left m hsucc
  have hBpos : 0 < B := by
    change 0 < m * bound
    exact Nat.mul_pos hm hbound
  have hHpos : 0 < H := by
    change 0 < 2 * B
    exact Nat.mul_pos (Nat.succ_pos 1) hBpos
  have hcost0 :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (birthStep M hm) 1 (renewalPotential rank) hsuper
      (.active x) H
  have hcost :
      1 * truncatedActiveCostNumerator (birthStep M hm) (.active x) H ≤
        B * m ^ H := by
    calc
      1 * truncatedActiveCostNumerator (birthStep M hm) (.active x) H ≤
          m ^ H * renewalPotential rank (.active x) := hcost0
      _ ≤ m ^ H * B := Nat.mul_le_mul_left _ hpotential
      _ = B * m ^ H := Nat.mul_comm _ _
  have hactive :
      2 * activeCount (birthStep M hm) (.active x) H ≤ m ^ H := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
      (birthStep M hm) (.active x) (den := 1) (num := B) (L := H)
    · exact hHpos
    · exact Nat.succ_pos 0
    · exact hcost
    · change 2 * renewalBudget m bound ≤ renewalHorizon m bound * 1
      rw [Nat.mul_one]
      rw [renewalHorizon] <;> exact Nat.le_refl _
  have hfailure :
      failureCount (birthStep M hm) (.active x) H = 0 :=
    BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
      (birthStep M hm) (birthStep_ne_failure M hm) x H
  have hpartition :=
    node_count_partition (birthStep M hm) (.active x) H
  change
    m ^ H ≤ 2 * successCount (birthStep M hm) (.active x) H
  omega

#print axioms BirthSweepSpec.setAt_eq
#print axioms BirthSweepSpec.setAt_ne
#print axioms BirthSweepSpec.commitEvent_parts
#print axioms BirthSweepSpec.launchEvent_parts
#print axioms BirthSweepSpec.commitEvent_of_parts
#print axioms BirthSweepSpec.launchEvent_of_parts
#print axioms BirthSweepSpec.sweepStep_invalidate
#print axioms BirthSweepSpec.sweepStep_commit
#print axioms BirthSweepSpec.sweepStep_launch
#print axioms BirthSweepSpec.sweepStep_service
#print axioms BirthSweepSpec.commit_consumes_permission
#print axioms BirthSweepSpec.launch_clears_permission
#print axioms BirthSweepSpec.forget_taggedStep
#print axioms BirthSweepSpec.emptyGhost_lineage
#print axioms BirthSweepSpec.launchGhost_lineage
#print axioms BirthSweepSpec.markGhost_lineage
#print axioms BirthSweepSpec.serviceGhost_lineage
#print axioms BirthSweepSpec.ghostStep_preserves_lineage
#print axioms BirthSweepSpec.taggedStep_launch_lineage
#print axioms BirthSweepSpec.taggedStep_preserves_lineage
#print axioms BirthSweepSpec.runTagged_preserves_lineage
#print axioms BirthSweepSpec.Lineage.prefix
#print axioms BirthSweepSpec.erase_prefix_provenance
#print axioms BirthSweepSpec.scrub_before_reuse
#print axioms BirthSweepSpec.scrub_before_reuse_three
#print axioms BirthSweepSpec.three_colors_without_scrub_collision
#print axioms BirthSweepSpec.birthEvent_of_commit
#print axioms BirthSweepSpec.birthEvent_of_secondBirth
#print axioms BirthSweepSpec.birthStep_success
#print axioms BirthSweepSpec.birthStep_active
#print axioms BirthSweepSpec.commit_sound_after_wash
#print axioms BirthSweepSpec.persistent_leader_blocks_commit
#print axioms BirthSweepSpec.leaderless_aligned_second_birth
#print axioms BirthSweepSpec.leaderless_nonAligned_rank_progress
#print axioms BirthSweepSpec.renewal_target_progress
#print axioms BirthSweepSpec.renewal_rank_nonincrease
#print axioms BirthSweepSpec.renewal_rank_lt_bound
#print axioms BirthSweepSpec.mul_eq_self_add_pred_mul
#print axioms BirthSweepSpec.renewalPotential_super
#print axioms BirthSweepSpec.birthStep_ne_failure
#print axioms BirthSweepSpec.leaderless_service_renewal_mass

end BirthSweepSpec
