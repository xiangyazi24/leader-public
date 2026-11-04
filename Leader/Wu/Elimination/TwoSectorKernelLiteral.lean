import Leader.Wu.Elimination.TwoSectorKernelSpec
import Leader.Wu.Protocol.Repairs
import Leader.Wu.Safety.SignalCoherence

/-!
# A literal four-field instance of `LDKernelSpec.LDKernel`

`Leader.Wu.Elimination.TwoSectorKernelSpec` fixes a data-only adapter `LDKernel n a b` and derives
the sealed two-sector closure and the redirected first-moment counting from two
hypothesis structures, `ClosureCaseLaws` and `TargetCycleLaws`.  This module
builds an actual `LDKernel` out of the repository's literal Algorithm-15
kernel and discharges the fields that are genuinely provable from locality.

## What the repository actually has

The four control fields `(leader, bullet, shield, signal_B)` named by
`RESEARCH_AGENDA.md` section R1 live on `AgentState` (`Leader/Wu/Protocol/State.lean`),
with `bullet : Fin 3` (`0` absent, `1` dummy, `2` live) and
`signal_B : Fin 2`.  `PPLLCompleteMultiLeaderCleanup.CleanupPhysicalView` is
the repository's own physical projection of exactly these plus `label`.

The literal transition is `PPLLRepair.eliminateLeadersNoCollision`
(`Leader/Wu/Protocol/Repairs.lean`), the audited no-collision repair of Algorithm 15.  Its
three stages are FIRE, MOVE and SIGNAL:

* FIRE: an initiator leader with `signal_B = 1` takes `bullet := 2`,
  `shield := true`, `signal_B := 0`; a responder leader with `signal_B = 1`
  takes `bullet := 1`, `shield := false`, `signal_B := 0`.
* MOVE: a responder bullet next to an initiator leader deletes that leader
  exactly when the bullet is live and the leader is unshielded; a responder
  bullet next to a follower initiator moves to the initiator (label aligned)
  or is destroyed (label unaligned).
* SIGNAL: on an aligned edge or under a leader initiator the responder takes
  `signal_B := max (l.signal_B) (r.signal_B) (l.leader)`, clamped to `0` when
  the responder carries a live bullet.

So bullets travel towards *decreasing* ring index and the absence signal
travels towards *increasing* ring index.  A leader therefore shoots at the
leader below it and is re-armed by that same leader's returning signal.

The ring update below is definitionally
`PPLLNoCheckBirthConditionTwoGlobal.noCollisionStep`; that module is not
imported because its transitive dependency chain is unbuilt and because its
global preservation theorem assumes `OutputSafeConfig`, which requires a
*unique* leader and is therefore unusable for `LD(c)`, a statement about three
leaders.

## Block geometry

Three cyclically consecutive leaders sit at ring offsets `0`, `b` and `a + b`
from `low`:

* `victim := pos 0`  -- the leader the target shoots at;
* `target := pos b`  -- the shared middle leader `j`;
* `attacker := pos (a+b)` -- the leader that shoots at the target.

The target sector has length `b` (local indices `0 .. b`); the attacker sector
has length `a` (local indices `0 .. a`, i.e. ring offsets `b .. a+b`).
-/

namespace LDKernelInstance

set_option autoImplicit false

open LDKernelSpec
open FiniteUniformStoppingTree

/-! ## The block frame -/

/-- Placement data for one `LD(c)` three-leader block on a directed ring.
`hblock` says the third gap has length at least two, so the block's own cells
are disjoint from the outside cell that fires into `victim`. -/
structure BlockFrame (n a b ψ : Nat) where
  ring : DirectedRing n
  hpsi : 0 < ψ
  ha : 0 < a
  hb : 0 < b
  hblock : a + b + 1 < n
  low : Fin n

namespace BlockFrame

variable {n a b ψ : Nat}

/-- Total block length: the target gap plus the attacker gap. -/
def blockLen (_F : BlockFrame n a b ψ) : Nat := a + b

/-- The ring cell at clockwise offset `t` from the block's low endpoint. -/
def pos (F : BlockFrame n a b ψ) (t : Nat) : Fin n :=
  ⟨(F.low.val + t) % n, Nat.mod_lt _ F.ring.hn⟩

/-- The clockwise offset of a ring cell from the block's low endpoint. -/
def off (F : BlockFrame n a b ψ) (x : Fin n) : Nat :=
  (x.val + n - F.low.val) % n

theorem off_lt (F : BlockFrame n a b ψ) (x : Fin n) : F.off x < n :=
  Nat.mod_lt _ F.ring.hn

theorem off_pos (F : BlockFrame n a b ψ) (t : Nat) (ht : t < n) :
    F.off (F.pos t) = t := by
  have hlow : F.low.val < n := F.low.isLt
  show ((F.low.val + t) % n + n - F.low.val) % n = t
  by_cases h : F.low.val + t < n
  · have e1 : (F.low.val + t) % n = F.low.val + t := Nat.mod_eq_of_lt h
    rw [e1]
    have e2 : F.low.val + t + n - F.low.val = t + n := by omega
    rw [e2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ht
  · have h2 : n ≤ F.low.val + t := by omega
    have e1 : (F.low.val + t) % n = F.low.val + t - n := by
      rw [Nat.mod_eq_sub_mod h2]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + t - n + n - F.low.val = t := by omega
    rw [e2]
    exact Nat.mod_eq_of_lt ht

theorem pos_off (F : BlockFrame n a b ψ) (x : Fin n) : F.pos (F.off x) = x := by
  have hA : F.low.val < n := F.low.isLt
  have hX : x.val < n := x.isLt
  apply Fin.ext
  show (F.low.val + (x.val + n - F.low.val) % n) % n = x.val
  by_cases h : F.low.val ≤ x.val
  · have h1 : n ≤ x.val + n - F.low.val := by omega
    have e1 : (x.val + n - F.low.val) % n = x.val + n - F.low.val - n := by
      rw [Nat.mod_eq_sub_mod h1]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + (x.val + n - F.low.val - n) = x.val := by omega
    rw [e2]
    exact Nat.mod_eq_of_lt hX
  · have e1 : (x.val + n - F.low.val) % n = x.val + n - F.low.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [e1]
    have e2 : F.low.val + (x.val + n - F.low.val) = x.val + n := by omega
    rw [e2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hX

theorem pos_inj (F : BlockFrame n a b ψ) {s t : Nat} (hs : s < n) (ht : t < n)
    (h : F.pos s = F.pos t) : s = t := by
  have h' := congrArg F.off h
  rwa [off_pos F s hs, off_pos F t ht] at h'

theorem pos_ne (F : BlockFrame n a b ψ) {s t : Nat} (hs : s < n) (ht : t < n)
    (h : s ≠ t) : F.pos s ≠ F.pos t := fun heq => h (pos_inj F hs ht heq)

theorem pos_n (F : BlockFrame n a b ψ) : F.pos n = F.pos 0 := by
  apply Fin.ext
  show (F.low.val + n) % n = (F.low.val + 0) % n
  rw [Nat.add_mod_right, Nat.add_zero]

theorem rightNeighbor_pos (F : BlockFrame n a b ψ) (t : Nat) :
    F.ring.rightNeighbor (F.pos t) = F.pos (t + 1) := by
  apply Fin.ext
  show ((F.low.val + t) % n + 1) % n = (F.low.val + (t + 1)) % n
  rw [Nat.mod_add_mod]
  rw [Nat.add_assoc]

/-- The three tagged leaders of the block. -/
def victim (F : BlockFrame n a b ψ) : Fin n := F.pos 0
def target (F : BlockFrame n a b ψ) : Fin n := F.pos b
def attacker (F : BlockFrame n a b ψ) : Fin n := F.pos (a + b)

end BlockFrame

/-! ## The raw ring step -/

variable {n a b ψ : Nat}

/-- One interaction of the literal four-field Algorithm-15 kernel at edge `e`.
Definitionally equal to `noCollisionStep`. -/
def ldStep (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) (e : Fin n) :
    Fin n → AgentState ψ :=
  updatePair C e (F.ring.rightNeighbor e)
    (PPLLRepair.eliminateLeadersNoCollision F.hpsi (C e)
      (C (F.ring.rightNeighbor e)))

theorem ldStep_other (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e k : Fin n) (h1 : k ≠ e) (h2 : k ≠ F.ring.rightNeighbor e) :
    ldStep F C e k = C k :=
  updatePair_other C e (F.ring.rightNeighbor e) k _ h1 h2

/-- Locality in block coordinates: a cell whose offset differs from both
endpoint offsets of the fired edge is untouched. -/
theorem ldStep_pos_eq (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (s r : Nat) (hs : s < n) (hr : r < n)
    (hre : F.ring.rightNeighbor e = F.pos r)
    (h1 : s ≠ F.off e) (h2 : s ≠ r) :
    ldStep F C e (F.pos s) = C (F.pos s) := by
  apply ldStep_other
  · intro h
    rw [← F.pos_off e] at h
    exact h1 (F.pos_inj hs (F.off_lt e) h)
  · rw [hre]
    exact F.pos_ne hs hr h2


/-! ## Sector views

Each sector is summarised by two `Nat`-valued functions of the *sector-local*
index.  Out-of-range indices are pinned to `0`, so that two configurations
agreeing on the sector cells have *equal* view functions, not merely pointwise
equal ones.  That is what makes the locality arguments below one-line
rewrites. -/

/-- Bullet value at target-sector index `t` (`t = b` is the target's own cell,
`t = 1` the cell adjacent to the victim). -/
def tgtBullet (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Nat → Nat :=
  fun t => if 1 ≤ t ∧ t ≤ b then (C (F.pos t)).bullet.val else 0

/-- Absence-signal value at target-sector index `t`. -/
def tgtSig (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Nat → Nat :=
  fun t => if 1 ≤ t ∧ t ≤ b then (C (F.pos t)).signal_B.val else 0

/-- Bullet value at attacker-sector index `t` (ring offset `b + t`). -/
def atkBullet (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Nat → Nat :=
  fun t => if 1 ≤ t ∧ t ≤ a then (C (F.pos (b + t))).bullet.val else 0

/-- Absence-signal value at attacker-sector index `t`. -/
def atkSig (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Nat → Nat :=
  fun t => if 1 ≤ t ∧ t ≤ a then (C (F.pos (b + t))).signal_B.val else 0

theorem tgtBullet_congr (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ b → D (F.pos t) = C (F.pos t)) :
    tgtBullet F D = tgtBullet F C := by
  funext t
  simp only [tgtBullet]
  split
  · rename_i hh
    rw [h t hh.1 hh.2]
  · rfl

theorem tgtSig_congr (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ b → D (F.pos t) = C (F.pos t)) :
    tgtSig F D = tgtSig F C := by
  funext t
  simp only [tgtSig]
  split
  · rename_i hh
    rw [h t hh.1 hh.2]
  · rfl

theorem atkBullet_congr (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ a → D (F.pos (b + t)) = C (F.pos (b + t))) :
    atkBullet F D = atkBullet F C := by
  funext t
  simp only [atkBullet]
  split
  · rename_i hh
    rw [h t hh.1 hh.2]
  · rfl

theorem atkSig_congr (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ a → D (F.pos (b + t)) = C (F.pos (b + t))) :
    atkSig F D = atkSig F C := by
  funext t
  simp only [atkSig]
  split
  · rename_i hh
    rw [h t hh.1 hh.2]
  · rfl

/-! ## Reading the phase off the four fields -/

/-- Least sector index in `[1, m]` carrying a bullet, `0` if there is none.
This is the *leading* bullet: the one closest to the receiving leader, which
is the one whose progress edge the rank argument charges. -/
def leastBullet (bv : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
      if leastBullet bv m ≠ 0 then leastBullet bv m
      else if bv (m + 1) ≠ 0 then m + 1 else 0

/-- Greatest sector index in `[1, m]` carrying the absence signal, `0` if there
is none.  The signal set is a down-set in a sealed sector, so this is the
position of the returning front. -/
def topSignal (sv : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => if sv (m + 1) = 1 then m + 1 else topSignal sv m

theorem leastBullet_le (bv : Nat → Nat) (m : Nat) : leastBullet bv m ≤ m := by
  induction m with
  | zero => simp [leastBullet]
  | succ m ih =>
      simp only [leastBullet]
      split
      · omega
      · split
        · exact Nat.le_refl _
        · omega

theorem topSignal_le (sv : Nat → Nat) (m : Nat) : topSignal sv m ≤ m := by
  induction m with
  | zero => simp [topSignal]
  | succ m ih =>
      simp only [topSignal]
      split
      · exact Nat.le_refl _
      · omega

/-- The clean-phase summary of one sector.

`dummy p`/`live p` mean the sector's single bullet stands at sector index
`d - p`, so `p = 0` is "just fired" and `p = d - 1` is "adjacent to the
receiving leader"; `ret q` means the returning signal front stands at sector
index `d - q`; `ready` means the front has reached the firing leader's own
cell and no bullet is left.  This matches `LDKernelSpec.targetDebt`.

Two total-function conventions, both debt-faithful:

* a *live* bullet at index `d` (the firing leader's own cell, the state
  immediately after an initiator FIRE) has no `CleanPhase` constructor,
  because `CleanPhase.live` requires `0 < p`; it is reported as `dummy 0`,
  which carries the identical `targetDebt`;
* a sector with neither bullet nor signal is reported as `dummy 0`, the
  maximal debt, since a whole cycle is still outstanding. -/
def sectorPhase (bv sv : Nat → Nat) (d : Nat) (hd : 0 < d) : CleanPhase d :=
  if ht : 0 < leastBullet bv d then
    if hl : bv (leastBullet bv d) = 2 ∧ leastBullet bv d < d then
      .live (d - leastBullet bv d) (by omega) (by omega)
    else .dummy (d - leastBullet bv d) (by omega)
  else if hs : 0 < topSignal sv d ∧ topSignal sv d < d then
    .ret (d - topSignal sv d) (by omega) (by omega)
  else if topSignal sv d = d then .ready
  else .dummy 0 (by omega)

/-! ## The sealed clean normal form of one sector -/

/-- One sector carries at most one token.  `bulletClears` records that a
descending bullet erases the absence signal from every cell at or above its own
position (the MOVE stage sets `l.signal_B := 0`), so together with
`signalDownSet` a sector containing a bullet contains no signal at all. -/
structure SectorSealed (bv sv : Nat → Nat) (d : Nat) : Prop where
  atMostOneBullet : ∀ t u, 1 ≤ t → t ≤ d → 1 ≤ u → u ≤ d →
    bv t ≠ 0 → bv u ≠ 0 → t = u
  signalDownSet : ∀ s t, 1 ≤ s → s ≤ t → t ≤ d → sv t = 1 → sv s = 1
  bulletClears : ∀ t s, 1 ≤ t → t ≤ d → t ≤ s → s ≤ d → bv t ≠ 0 → sv s = 0

/-- Target-sector lineage: the sector is sealed and leader-free strictly
between the victim and the target. -/
def TgtSealed (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Prop :=
  SectorSealed (tgtBullet F C) (tgtSig F C) b ∧
    ∀ t, 1 ≤ t → t < b → (C (F.pos t)).leader = false

/-- Attacker-sector lineage: the sector is sealed and leader-free strictly
between the target and the attacker. -/
def AtkSealed (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Prop :=
  SectorSealed (atkBullet F C) (atkSig F C) a ∧
    ∀ t, 1 ≤ t → t < a → (C (F.pos (b + t))).leader = false

/-- The shared middle-leader constraint.  Besides the three tagged leaders
being alive, it pins each shooter's `shield` bit to the kind of token that
shooter currently has outstanding: a leader that fired live is shielded, a
leader that fired a dummy is not.  This is exactly the shield cycle that
`LDC_PROGRESS.md` identifies as the coupling between the two gaps. -/
def MiddleShared (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Prop :=
  (C F.victim).leader = true ∧
  (C F.target).leader = true ∧
  (C F.attacker).leader = true ∧
  (∀ t, 1 ≤ t → t ≤ b → (C (F.pos t)).bullet.val = 2 →
    (C F.target).shield = true) ∧
  (∀ t, 1 ≤ t → t ≤ b → (C (F.pos t)).bullet.val = 1 →
    (C F.target).shield = false) ∧
  (∀ t, 1 ≤ t → t ≤ a → (C (F.pos (b + t))).bullet.val = 2 →
    (C F.attacker).shield = true) ∧
  (∀ t, 1 ≤ t → t ≤ a → (C (F.pos (b + t))).bullet.val = 1 →
    (C F.attacker).shield = false)

/-! ## Stopping, service and the case split -/

/-- The `LD(c)` stopping event: one of the three tagged leaders has lost its
leader bit. -/
def ldDeleted (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Bool :=
  !((C F.victim).leader && (C F.target).leader && (C F.attacker).leader)

/-- Sector index of the initiator of the target's unique current progress
edge, if any.  A bullet at index `t` advances across the edge whose initiator
sits at index `t - 1`; a signal front at index `s` advances across the edge
whose initiator sits at index `s`. -/
def serviceIdx (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) :
    Option Nat :=
  match sectorPhase (tgtBullet F C) (tgtSig F C) b F.hb with
  | .ready => none
  | .dummy p _ => some (b - p - 1)
  | .live p _ _ => some (b - p - 1)
  | .ret q _ _ => some (b - q)

/-- The unique currently required progress edge of the target's own sector. -/
def ldTargetService (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) : Bool :=
  match serviceIdx F C with
  | none => false
  | some t => decide (e = F.pos t)

/-- Positional primary-effect classification of a raw scheduler symbol.
`leftIngress` is the edge entering the victim from the third gap;
`rightEgress` is the attacker's own outgoing edge; `middle` is the pair of
edges incident to the shared middle leader; `signalProp` is an in-block edge
with no bullet to move. -/
def ldCaseOf (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) (e : Fin n) :
    BlockRawCase :=
  if F.off e + 1 = n then .leftIngress
  else if a + b < F.off e then .outside
  else if F.off e = a + b then .rightEgress
  else if F.off e + 1 = b ∨ F.off e = b then .middle
  else if (C (F.pos (F.off e + 1))).bullet.val = 0 then .signalProp
  else if F.off e < b then .tgtInterior
  else .atkInterior

/-! ## The instance -/

/-- The literal four-field `LD(c)` kernel packaged as an `LDKernel`. -/
def ldKernel (F : BlockFrame n a b ψ) : LDKernel n a b where
  State := Fin n → AgentState ψ
  rawStep := ldStep F
  deleted := ldDeleted F
  atkPhase := fun C => sectorPhase (atkBullet F C) (atkSig F C) a F.ha
  tgtPhase := fun C => sectorPhase (tgtBullet F C) (tgtSig F C) b F.hb
  atkLineage := fun C _ => AtkSealed F C
  tgtLineage := fun C _ => TgtSealed F C
  middleShared := fun C _ _ => MiddleShared F C
  Lj := F.pos (b - 1)
  Rj := F.pos b
  Lj_ne_Rj := by
    have h1 : b - 1 < n := by have := F.hblock; omega
    have h2 : b < n := by have := F.hblock; omega
    exact F.pos_ne h1 h2 (by have := F.hb; omega)
  targetService := ldTargetService F
  caseOf := ldCaseOf F


/-! ## Unfolding the instance -/

theorem sealed_iff (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) :
    SealedTwoSector (ldKernel F) C ↔
      (AtkSealed F C ∧ TgtSealed F C ∧ MiddleShared F C) := Iff.rfl

theorem survives_iff (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) :
    survives (ldKernel F) C e ↔ ldDeleted F (ldStep F C e) ≠ true := Iff.rfl

/-- The stopping event is exactly the loss of one tagged leader bit, so on the
survival event all three tagged leaders are still leaders after the step.
This discharges the leader conjuncts of `MiddleShared` in *every* case. -/
theorem leaders_of_survives (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (h : ldDeleted F (ldStep F C e) ≠ true) :
    (ldStep F C e F.victim).leader = true ∧
    (ldStep F C e F.target).leader = true ∧
    (ldStep F C e F.attacker).leader = true := by
  have key : ∀ x y z : Bool, (!(x && y && z)) ≠ true →
      x = true ∧ y = true ∧ z = true := by decide
  exact key _ _ _ h

/-! ## Locality of the raw step in block coordinates -/

theorem rightNeighbor_eq (F : BlockFrame n a b ψ) (e : Fin n) :
    F.ring.rightNeighbor e = F.pos (F.off e + 1) := by
  have h := F.rightNeighbor_pos (F.off e)
  rw [F.pos_off e] at h
  exact h

theorem rightNeighbor_eq_zero (F : BlockFrame n a b ψ) (e : Fin n)
    (h : F.off e + 1 = n) : F.ring.rightNeighbor e = F.pos 0 := by
  rw [rightNeighbor_eq, h, F.pos_n]

/-- An edge with both endpoints outside the block leaves every block cell,
including the victim's, untouched. -/
theorem block_fixed_of_outside (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hgt : a + b < F.off e) (hne : F.off e + 1 ≠ n) :
    ∀ s, s ≤ a + b → ldStep F C e (F.pos s) = C (F.pos s) := by
  intro s hs
  have hoe := F.off_lt e
  have hbl := F.hblock
  exact ldStep_pos_eq F C e s (F.off e + 1) (by omega) (by omega)
    (rightNeighbor_eq F e) (by omega) (by omega)

/-- The edge entering the victim from the third gap touches only the victim's
own cell, which carries no sector index. -/
theorem block_fixed_of_leftIngress (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n) (h : F.off e + 1 = n) :
    ∀ s, 1 ≤ s → s ≤ a + b → ldStep F C e (F.pos s) = C (F.pos s) := by
  intro s h1 h2
  have hbl := F.hblock
  exact ldStep_pos_eq F C e s 0 (by omega) (by omega)
    (rightNeighbor_eq_zero F e h) (by omega) (by omega)

/-! ## Transport of the sealed normal form along fixed block cells -/

/-- If a step fixes every block cell with a positive sector index and keeps the
three tagged leader bits, the whole sealed two-sector normal form transports.
The victim's own cell (sector index `0`) is deliberately excluded: it carries
no sector observable, only the leader bit that `survives` already supplies. -/
theorem sealed_of_block_fixed (F : BlockFrame n a b ψ)
    (C D : Fin n → AgentState ψ)
    (hfix : ∀ s, 1 ≤ s → s ≤ a + b → D (F.pos s) = C (F.pos s))
    (hV : (D F.victim).leader = true)
    (hJ : (D F.target).leader = true)
    (hA : (D F.attacker).leader = true)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C) :
    AtkSealed F D ∧ TgtSealed F D ∧ MiddleShared F D := by
  have hb := F.hb
  have ha := F.ha
  have htcell : ∀ t, 1 ≤ t → t ≤ b → D (F.pos t) = C (F.pos t) := by
    intro t h1 h2; exact hfix t h1 (by omega)
  have hacell : ∀ t, 1 ≤ t → t ≤ a → D (F.pos (b + t)) = C (F.pos (b + t)) := by
    intro t h1 h2; exact hfix (b + t) (by omega) (by omega)
  have hJcell : D F.target = C F.target := hfix b (by omega) (by omega)
  have hAcell : D F.attacker = C F.attacker := by
    have := hfix (a + b) (by omega) (by omega)
    exact this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [atkBullet_congr F C D hacell, atkSig_congr F C D hacell]
    exact hAtk.1
  · intro t h1 h2
    rw [hacell t h1 (by omega)]
    exact hAtk.2 t h1 h2
  · rw [tgtBullet_congr F C D htcell, tgtSig_congr F C D htcell]
    exact hTgt.1
  · intro t h1 h2
    rw [htcell t h1 (by omega)]
    exact hTgt.2 t h1 h2
  · refine ⟨hV, hJ, hA, ?_, ?_, ?_, ?_⟩
    · intro t h1 h2 hbul
      rw [hJcell]
      exact hMid.2.2.2.1 t h1 h2 (by rw [htcell t h1 h2] at hbul; exact hbul)
    · intro t h1 h2 hbul
      rw [hJcell]
      exact hMid.2.2.2.2.1 t h1 h2 (by rw [htcell t h1 h2] at hbul; exact hbul)
    · intro t h1 h2 hbul
      rw [hAcell]
      exact hMid.2.2.2.2.2.1 t h1 h2 (by rw [hacell t h1 h2] at hbul; exact hbul)
    · intro t h1 h2 hbul
      rw [hAcell]
      exact hMid.2.2.2.2.2.2 t h1 h2 (by rw [hacell t h1 h2] at hbul; exact hbul)


/-! ## Inverting the positional case split -/

theorem off_of_leftIngress (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.leftIngress) :
    F.off e + 1 = n := by
  apply Classical.byContradiction
  intro h1
  unfold ldCaseOf at hcase
  rw [if_neg h1] at hcase
  by_cases h2 : a + b < F.off e
  · rw [if_pos h2] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h2] at hcase
  by_cases h3 : F.off e = a + b
  · rw [if_pos h3] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h3] at hcase
  by_cases h4 : F.off e + 1 = b ∨ F.off e = b
  · rw [if_pos h4] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h4] at hcase
  by_cases h5 : (C (F.pos (F.off e + 1))).bullet.val = 0
  · rw [if_pos h5] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h5] at hcase
  by_cases h6 : F.off e < b
  · rw [if_pos h6] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h6] at hcase
  exact BlockRawCase.noConfusion hcase

theorem off_of_outside (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.outside) :
    F.off e + 1 ≠ n ∧ a + b < F.off e := by
  unfold ldCaseOf at hcase
  by_cases h1 : F.off e + 1 = n
  · rw [if_pos h1] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h1] at hcase
  by_cases h2 : a + b < F.off e
  · exact ⟨h1, h2⟩
  rw [if_neg h2] at hcase
  by_cases h3 : F.off e = a + b
  · rw [if_pos h3] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h3] at hcase
  by_cases h4 : F.off e + 1 = b ∨ F.off e = b
  · rw [if_pos h4] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h4] at hcase
  by_cases h5 : (C (F.pos (F.off e + 1))).bullet.val = 0
  · rw [if_pos h5] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h5] at hcase
  by_cases h6 : F.off e < b
  · rw [if_pos h6] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h6] at hcase
  exact BlockRawCase.noConfusion hcase

/-! ## The two closure laws that are actually provable here -/

/-- `ClosureCaseLaws.outside` for the literal kernel: pure locality. -/
theorem closure_outside (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.outside)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C)
    (hsurv : ldDeleted F (ldStep F C e) ≠ true) :
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e) := by
  obtain ⟨h1, h2⟩ := off_of_outside F C e hcase
  obtain ⟨hV, hJ, hA⟩ := leaders_of_survives F C e hsurv
  exact sealed_of_block_fixed F C (ldStep F C e)
    (fun s _ hs => block_fixed_of_outside F C e h2 h1 s hs) hV hJ hA hAtk hTgt hMid

/-- `ClosureCaseLaws.leftIngress` for the literal kernel.  The edge entering the
victim from the third gap can only rewrite the victim's own cell, which carries
no sector observable, and it cannot clear a responder leader bit; the surviving
leader bits come from the stopping-event hypothesis. -/
theorem closure_leftIngress (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.leftIngress)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C)
    (hsurv : ldDeleted F (ldStep F C e) ≠ true) :
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e) := by
  have h1 := off_of_leftIngress F C e hcase
  obtain ⟨hV, hJ, hA⟩ := leaders_of_survives F C e hsurv
  exact sealed_of_block_fixed F C (ldStep F C e)
    (block_fixed_of_leftIngress F C e h1) hV hJ hA hAtk hTgt hMid


/-! ## Literal-kernel facts used by the right-egress case

At an edge whose initiator is a surviving leader, the MOVE stage cannot touch
the initiator: its deletion branch would clear the leader bit (excluded by the
survival hypothesis) and its transport branch is guarded on a *follower*
initiator.  So the initiator's new cell is exactly the FIRE output. -/

theorem fire_left_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (PPLLRepair.eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader := by
  unfold PPLLRepair.eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

theorem fire_left_eq (hψ : ψ > 0) (l r : AgentState ψ) :
    (PPLLRepair.eliminateLeadersNoCollisionFire hψ l r).1 =
      if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
        { l with bullet := ⟨2, by omega⟩, shield := true,
                 signal_B := ⟨0, by omega⟩ }
      else l := rfl

theorem move_left_of_leader (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true)
    (hq : (PPLLRepair.eliminateLeadersNoCollisionMove nl l r).1.leader = true) :
    (PPLLRepair.eliminateLeadersNoCollisionMove nl l r).1 = l := by
  revert hq
  unfold PPLLRepair.eliminateLeadersNoCollisionMove
  split
  · split
    · intro hq; simp at hq
    · intro _; rfl
  · split
    · rename_i h
      exfalso
      simp [hl] at h
    · intro _; rfl

theorem kernel_left_of_leader (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true)
    (hq : (PPLLRepair.eliminateLeadersNoCollision hψ l r).1.leader = true) :
    (PPLLRepair.eliminateLeadersNoCollision hψ l r).1 =
      (PPLLRepair.eliminateLeadersNoCollisionFire hψ l r).1 := by
  have hst : (PPLLRepair.eliminateLeadersNoCollision hψ l r).1 =
      (PPLLRepair.eliminateLeadersNoCollisionMove
        (⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ : Fin ψ)
        (PPLLRepair.eliminateLeadersNoCollisionFire hψ l r).1
        (PPLLRepair.eliminateLeadersNoCollisionFire hψ l r).2).1 := by
    rw [PPLLRepair.eliminateLeadersNoCollision_eq_staged]
    rfl
  rw [hst]
  apply move_left_of_leader
  · rw [fire_left_leader]; exact hl
  · rw [← hst]; exact hq


/-! ## Sector-view evaluation -/

theorem tgtBullet_val (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ b) :
    tgtBullet F C t = (C (F.pos t)).bullet.val := by
  unfold tgtBullet; rw [if_pos ⟨h1, h2⟩]

theorem tgtSig_val (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ b) :
    tgtSig F C t = (C (F.pos t)).signal_B.val := by
  unfold tgtSig; rw [if_pos ⟨h1, h2⟩]

theorem atkBullet_val (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ a) :
    atkBullet F C t = (C (F.pos (b + t))).bullet.val := by
  unfold atkBullet; rw [if_pos ⟨h1, h2⟩]

theorem atkSig_val (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ a) :
    atkSig F C t = (C (F.pos (b + t))).signal_B.val := by
  unfold atkSig; rw [if_pos ⟨h1, h2⟩]

/-! ## The right-egress closure law -/

theorem off_of_rightEgress (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.rightEgress) :
    F.off e = a + b ∧ F.off e + 1 ≠ n := by
  unfold ldCaseOf at hcase
  by_cases h1 : F.off e + 1 = n
  · rw [if_pos h1] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h1] at hcase
  by_cases h2 : a + b < F.off e
  · rw [if_pos h2] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h2] at hcase
  by_cases h3 : F.off e = a + b
  · exact ⟨h3, h1⟩
  rw [if_neg h3] at hcase
  by_cases h4 : F.off e + 1 = b ∨ F.off e = b
  · rw [if_pos h4] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h4] at hcase
  by_cases h5 : (C (F.pos (F.off e + 1))).bullet.val = 0
  · rw [if_pos h5] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h5] at hcase
  by_cases h6 : F.off e < b
  · rw [if_pos h6] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h6] at hcase
  exact BlockRawCase.noConfusion hcase

/-- `ClosureCaseLaws.rightEgress`, discharged against the literal kernel.

At the attacker's own outgoing edge the MOVE stage cannot alter a surviving
leader initiator, so the only possible change to the block is the attacker's
FIRE.  FIRE requires the attacker's own absence signal, which `bulletClears`
forbids whenever the attacker's gap already holds a bullet; hence the sector
was empty and the new live bullet is the unique token, with the matching
`shield := true`. -/
theorem closure_rightEgress (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hcase : ldCaseOf F C e = BlockRawCase.rightEgress)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C)
    (hsurv : ldDeleted F (ldStep F C e) ≠ true) :
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e) := by
  obtain ⟨h3, h1⟩ := off_of_rightEgress F C e hcase
  obtain ⟨hVl, hJl, hAl⟩ := leaders_of_survives F C e hsurv
  have ha := F.ha
  have hb := F.hb
  have hbl := F.hblock
  have hoe : F.off e < n := F.off_lt e
  have heA : e = F.attacker := by
    have hp := F.pos_off e
    rw [h3] at hp
    exact hp.symm
  have hpab : F.pos (a + b) = e := heA.symm
  have hpa : F.pos (b + a) = e := by
    rw [Nat.add_comm b a]; exact heA.symm
  -- every block cell strictly below the attacker is fixed
  have hfixlt : ∀ s, s < a + b → ldStep F C e (F.pos s) = C (F.pos s) := by
    intro s hs
    exact ldStep_pos_eq F C e s (F.off e + 1) (by omega) (by omega)
      (rightNeighbor_eq F e) (by omega) (by omega)
  -- the attacker's own cell is exactly the FIRE output
  have hAout : ldStep F C e e =
      (PPLLRepair.eliminateLeadersNoCollisionFire F.hpsi (C e)
        (C (F.ring.rightNeighbor e))).1 := by
    have hstep : ldStep F C e e =
        (PPLLRepair.eliminateLeadersNoCollision F.hpsi (C e)
          (C (F.ring.rightNeighbor e))).1 :=
      updatePair_initiator C e (F.ring.rightNeighbor e) _
    rw [hstep]
    refine kernel_left_of_leader F.hpsi (C e) (C (F.ring.rightNeighbor e))
      ?_ ?_
    · rw [heA]; exact hMid.2.2.1
    · have hAl2 := hAl
      rw [← heA] at hAl2
      rw [← hstep]
      exact hAl2
  by_cases hfire : (C e).leader = true ∧
      (C e).signal_B = (⟨1, by omega⟩ : Fin 2)
  · -- the attacker fires a fresh live bullet into an empty gap
    have hAnew : ldStep F C e e =
        { C e with bullet := (⟨2, by omega⟩ : Fin 3), shield := true,
                   signal_B := (⟨0, by omega⟩ : Fin 2) } := by
      rw [hAout, fire_left_eq, if_pos hfire]
    have hsigA : atkSig F C a = 1 := by
      rw [atkSig_val F C a (by omega) (by omega), hpa, hfire.2]
    have hempty : ∀ t, 1 ≤ t → t ≤ a → atkBullet F C t = 0 := by
      intro t ht1 ht2
      by_cases hz : atkBullet F C t = 0
      · exact hz
      · exact absurd (hAtk.1.bulletClears t a ht1 ht2 ht2 (Nat.le_refl a) hz)
          (by rw [hsigA]; exact (by decide))
    have hbvD : ∀ t, 1 ≤ t → t ≤ a →
        atkBullet F (ldStep F C e) t = if t = a then 2 else 0 := by
      intro t ht1 ht2
      rw [atkBullet_val F _ t ht1 ht2]
      by_cases hta : t = a
      · rw [if_pos hta]
        rw [hta, hpa, hAnew]
      · rw [if_neg hta]
        rw [hfixlt (b + t) (by omega)]
        have := hempty t ht1 ht2
        rwa [atkBullet_val F C t ht1 ht2] at this
    have hsvD : ∀ t, 1 ≤ t → t ≤ a →
        atkSig F (ldStep F C e) t = if t = a then 0 else atkSig F C t := by
      intro t ht1 ht2
      rw [atkSig_val F _ t ht1 ht2]
      by_cases hta : t = a
      · rw [if_pos hta, hta, hpa, hAnew]
      · rw [if_neg hta, hfixlt (b + t) (by omega), atkSig_val F C t ht1 ht2]
    have htcell : ∀ t, 1 ≤ t → t ≤ b →
        ldStep F C e (F.pos t) = C (F.pos t) := by
      intro t ht1 ht2; exact hfixlt t (by omega)
    have hJcell : ldStep F C e F.target = C F.target := hfixlt b (by omega)
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t u ht1 ht2 hu1 hu2 hbt hbu
      rw [hbvD t ht1 ht2] at hbt
      rw [hbvD u hu1 hu2] at hbu
      by_cases hta : t = a
      · by_cases hua : u = a
        · rw [hta, hua]
        · rw [if_neg hua] at hbu; exact absurd rfl hbu
      · rw [if_neg hta] at hbt; exact absurd rfl hbt
    · intro s t hs1 hst hta hsig
      rw [hsvD t (by omega) hta] at hsig
      by_cases hteq : t = a
      · rw [if_pos hteq] at hsig; exact absurd hsig (by decide)
      · rw [if_neg hteq] at hsig
        rw [hsvD s hs1 (by omega), if_neg (by omega)]
        exact hAtk.1.signalDownSet s t hs1 hst hta hsig
    · intro t s ht1 ht2 hts hs2 hbt
      rw [hbvD t ht1 ht2] at hbt
      by_cases hta : t = a
      · have hsa : s = a := by omega
        rw [hsvD s (by omega) hs2, if_pos hsa]
      · rw [if_neg hta] at hbt; exact absurd rfl hbt
    · intro t ht1 ht2
      rw [hfixlt (b + t) (by omega)]
      exact hAtk.2 t ht1 ht2
    · rw [tgtBullet_congr F C _ htcell, tgtSig_congr F C _ htcell]
      exact hTgt.1
    · intro t ht1 ht2
      rw [htcell t ht1 (by omega)]
      exact hTgt.2 t ht1 ht2
    · exact hVl
    · exact hJl
    · exact hAl
    · intro t ht1 ht2 hbul
      rw [hJcell]
      rw [htcell t ht1 ht2] at hbul
      exact hMid.2.2.2.1 t ht1 ht2 hbul
    · intro t ht1 ht2 hbul
      rw [hJcell]
      rw [htcell t ht1 ht2] at hbul
      exact hMid.2.2.2.2.1 t ht1 ht2 hbul
    · intro t ht1 ht2 _
      rw [← heA, hAnew]
    · intro t ht1 ht2 hbul
      exfalso
      have hv := hbvD t ht1 ht2
      rw [atkBullet_val F _ t ht1 ht2, hbul] at hv
      by_cases hta : t = a
      · rw [if_pos hta] at hv; exact absurd hv (by decide)
      · rw [if_neg hta] at hv; exact absurd hv (by decide)
  · -- the attacker does not fire, so the whole block is fixed
    have hAsame : ldStep F C e e = C e := by
      rw [hAout, fire_left_eq, if_neg hfire]
    refine sealed_of_block_fixed F C (ldStep F C e) ?_ hVl hJl hAl hAtk hTgt hMid
    intro s hs1 hs2
    by_cases hsa : s = a + b
    · rw [hsa, hpab]; exact hAsame
    · exact hfixlt s (by omega)

/-! ## The undischarged closure obligations

Each field below is the exact statement, fully unfolded against the literal
`PPLLRepair.eliminateLeadersNoCollision` kernel, of a `ClosureCaseLaws` case
that is *not* proved here.  Together they are the "sealed two-sector
clean-normal-form closure" recorded as open in `RESEARCH_AGENDA.md` R1 and in
research-map claim `LDR-ELIVE-LD-GATE`. -/
structure MissingLDLemmas (F : BlockFrame n a b ψ) : Prop where
  /-- A bullet move strictly inside the attacker's gap preserves the sealed
  normal form. -/
  atkInterior : ∀ (C : Fin n → AgentState ψ) (e : Fin n),
    ldCaseOf F C e = BlockRawCase.atkInterior →
    AtkSealed F C → TgtSealed F C → MiddleShared F C →
    ldDeleted F (ldStep F C e) ≠ true →
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e)
  /-- The two edges incident to the shared middle leader: the target's own
  firing (dummy as responder on `Lj`, live as initiator on `Rj`), the first
  move of its dummy, and the arrival of the attacker's bullet.  This is the
  case where the two gap processes are coupled through the target's `shield`
  bit. -/
  middle : ∀ (C : Fin n → AgentState ψ) (e : Fin n),
    ldCaseOf F C e = BlockRawCase.middle →
    AtkSealed F C → TgtSealed F C → MiddleShared F C →
    ldDeleted F (ldStep F C e) ≠ true →
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e)
  /-- A bullet move strictly inside the target's own gap, including the
  absorption or kill at the victim, preserves the sealed normal form. -/
  tgtInterior : ∀ (C : Fin n → AgentState ψ) (e : Fin n),
    ldCaseOf F C e = BlockRawCase.tgtInterior →
    AtkSealed F C → TgtSealed F C → MiddleShared F C →
    ldDeleted F (ldStep F C e) ≠ true →
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e)
  /-- An in-block edge whose responder carries no bullet: the SIGNAL stage
  advances the returning absence front by one cell. -/
  signalProp : ∀ (C : Fin n → AgentState ψ) (e : Fin n),
    ldCaseOf F C e = BlockRawCase.signalProp →
    AtkSealed F C → TgtSealed F C → MiddleShared F C →
    ldDeleted F (ldStep F C e) ≠ true →
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e)

/-- The full per-case closure package, conditional on the three undischarged
cases; `leftIngress`, `rightEgress` and `outside` are proved above. -/
theorem ldClosureLaws (F : BlockFrame n a b ψ) (M : MissingLDLemmas F) :
    ClosureCaseLaws (ldKernel F) where
  leftIngress := fun s e hc hseal hno =>
    closure_leftIngress F s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  atkInterior := fun s e hc hseal hno =>
    M.atkInterior s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  middle := fun s e hc hseal hno =>
    M.middle s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  tgtInterior := fun s e hc hseal hno =>
    M.tgtInterior s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  rightEgress := fun s e hc hseal hno =>
    closure_rightEgress F s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  signalProp := fun s e hc hseal hno =>
    M.signalProp s e hc hseal.1 hseal.2.1 hseal.2.2 hno
  outside := fun s e hc hseal hno =>
    closure_outside F s e hc hseal.1 hseal.2.1 hseal.2.2 hno

/-- L1 for the literal kernel, conditional on `MissingLDLemmas`. -/
theorem ld_sealed_closed (F : BlockFrame n a b ψ) (M : MissingLDLemmas F) :
    ∀ (s : Fin n → AgentState ψ) (e : Fin n),
      SealedTwoSector (ldKernel F) s → survives (ldKernel F) s e →
      SealedTwoSector (ldKernel F) (ldStep F s e) :=
  fun s e h1 h2 => sealedTwoSector_closed (ldKernel F) (ldClosureLaws F M) s e h1 h2


/-! ## The redirected service count is one-hot

`TargetCycleLaws.serviceUnique` is proved outright: `targetService` is the
indicator of a single edge, and at Ready it is the indicator of no edge, which
is also the only place where `redirect` is not the identity. -/

theorem ofFn_sum_zero {m : Nat} (f : Fin m → Nat) (h : ∀ i, f i = 0) :
    (List.ofFn f).sum = 0 := by
  rw [ofFn_sum_eq f (fun _ => 0) h, ofFn_sum_const]
  exact Nat.mul_zero m

theorem ofFn_sum_le_one : ∀ {m : Nat} (f : Fin m → Nat), (∀ i, f i ≤ 1) →
    (∀ i j, f i = 1 → f j = 1 → i = j) → (List.ofFn f).sum ≤ 1 := by
  intro m
  induction m with
  | zero => intro f _ _; simp
  | succ m ih =>
      intro f hle huniq
      rw [List.ofFn_succ, List.sum_cons]
      by_cases h0 : f 0 = 1
      · have htail : ∀ i : Fin m, f i.succ = 0 := by
          intro i
          have hb := hle i.succ
          by_cases h1 : f i.succ = 1
          · exfalso
            have heq := huniq 0 i.succ h0 h1
            have hval := congrArg Fin.val heq
            simp only [Fin.val_zero, Fin.val_succ] at hval
            omega
          · omega
        rw [ofFn_sum_zero (fun i : Fin m => f i.succ) htail]
        omega
      · have hz : f 0 = 0 := by have := hle 0; omega
        rw [hz, Nat.zero_add]
        refine ih (fun i : Fin m => f i.succ) (fun i => hle i.succ) ?_
        intro i j hi hj
        have heq := huniq i.succ j.succ hi hj
        have hval := congrArg Fin.val heq
        simp only [Fin.val_succ] at hval
        exact Fin.ext (by omega)

theorem isReady_eq {d : Nat} (p : CleanPhase d) (h : p.isReady = true) :
    p = CleanPhase.ready := by
  cases p with
  | ready => rfl
  | dummy p hp => exact absurd h (by simp [CleanPhase.isReady])
  | live p h0 h1 => exact absurd h (by simp [CleanPhase.isReady])
  | ret q h0 h1 => exact absurd h (by simp [CleanPhase.isReady])

theorem serviceIdx_none_of_ready (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ)
    (h : sectorPhase (tgtBullet F C) (tgtSig F C) b F.hb = CleanPhase.ready) :
    serviceIdx F C = none := by
  unfold serviceIdx
  rw [h]

theorem targetService_false_of_ready (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ)
    (h : sectorPhase (tgtBullet F C) (tgtSig F C) b F.hb = CleanPhase.ready)
    (e : Fin n) : ldTargetService F C e = false := by
  unfold ldTargetService
  rw [serviceIdx_none_of_ready F C h]

/-- At most one edge is the target's current progress edge. -/
theorem targetService_eq (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e1 e2 : Fin n) (h1 : ldTargetService F C e1 = true)
    (h2 : ldTargetService F C e2 = true) : e1 = e2 := by
  unfold ldTargetService at h1 h2
  cases hsi : serviceIdx F C with
  | none => rw [hsi] at h1; exact absurd h1 (by simp)
  | some t =>
      rw [hsi] at h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      rw [h1, h2]

theorem serviceCost_eq (F : BlockFrame n a b ψ) (s : Joint (ldKernel F))
    (e : Fin n) :
    serviceCost (ldKernel F) s e =
      if ldTargetService F s.cfg (redirect (ldKernel F) s.cfg e) = true then 1
      else 0 := rfl

theorem serviceCost_le_one (F : BlockFrame n a b ψ) (s : Joint (ldKernel F))
    (e : Fin n) : serviceCost (ldKernel F) s e ≤ 1 := by
  rw [serviceCost_eq]
  split
  · exact Nat.le_refl 1
  · exact Nat.zero_le 1

theorem redirect_eq_self (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (hr : ready (ldKernel F) C = false) (e : Fin n) :
    redirect (ldKernel F) C e = e := by
  unfold redirect
  rw [hr]
  simp

theorem serviceCost_zero_of_ready (F : BlockFrame n a b ψ)
    (s : Joint (ldKernel F)) (hr : ready (ldKernel F) s.cfg = true)
    (e : Fin n) : serviceCost (ldKernel F) s e = 0 := by
  have hp : sectorPhase (tgtBullet F s.cfg) (tgtSig F s.cfg) b F.hb =
      CleanPhase.ready := isReady_eq _ hr
  rw [serviceCost_eq,
    targetService_false_of_ready F s.cfg hp (redirect (ldKernel F) s.cfg e)]
  simp

theorem serviceCost_unique (F : BlockFrame n a b ψ) (s : Joint (ldKernel F))
    (e1 e2 : Fin n) (h1 : serviceCost (ldKernel F) s e1 = 1)
    (h2 : serviceCost (ldKernel F) s e2 = 1) : e1 = e2 := by
  cases hr : ready (ldKernel F) s.cfg with
  | true =>
      exfalso
      rw [serviceCost_zero_of_ready F s hr e1] at h1
      exact absurd h1 (by decide)
  | false =>
      rw [serviceCost_eq, redirect_eq_self F s.cfg hr] at h1 h2
      have g1 : ldTargetService F s.cfg e1 = true := by
        by_cases hc : ldTargetService F s.cfg e1 = true
        · exact hc
        · rw [if_neg hc] at h1; exact absurd h1 (by decide)
      have g2 : ldTargetService F s.cfg e2 = true := by
        by_cases hc : ldTargetService F s.cfg e2 = true
        · exact hc
        · rw [if_neg hc] at h2; exact absurd h2 (by decide)
      exact targetService_eq F s.cfg e1 e2 g1 g2

/-- `TargetCycleLaws.serviceUnique`, discharged. -/
theorem ldServiceUnique (F : BlockFrame n a b ψ) :
    ∀ s : Joint (ldKernel F),
      (List.ofFn (fun e : Fin n => serviceCost (ldKernel F) s e)).sum ≤ 1 :=
  fun s => ofFn_sum_le_one _ (fun e => serviceCost_le_one F s e)
    (fun e1 e2 h1 h2 => serviceCost_unique F s e1 e2 h1 h2)


/-! ## The undischarged target-cycle obligation

`TargetCycleLaws` has two fields.  `serviceUnique` is proved above.  The
remaining one is the redirected service-count interface recorded as open in
`RESEARCH_AGENDA.md` R1 (`(2b-1) * E_Q[N] <= E_Q[tau]/n`).

Two fidelity notes discovered while building this instance, both of which the
credit obligation has to absorb:

* `LDKernelSpec.CleanPhase` has no `live 0` constructor, while an initiator
  FIRE on `Rj` does leave a *live* bullet on the target's own cell.  That state
  is reported here as `dummy 0`, which carries the identical
  `LDKernelSpec.targetDebt`, so the credit accounting is unaffected; only the
  constructor name is.
* The literal kernel runs FIRE and MOVE inside one interaction, so a responder
  dummy firing on `Lj` immediately advances to target-sector index `b - 1`.
  The phase `dummy 0` is therefore *not* the state right after a clean dummy
  firing; the reachable post-firing phase is `dummy 1`.  The counting theorems
  of `LDKernelSpec` are stated from `tgtPhase = dummy 0` (credit `0`), so
  applying them to a real post-dummy start loses one unit of credit out of
  `2b - 1`. -/
structure MissingTargetCredit (F : BlockFrame n a b ψ)
    (M : MissingLDLemmas F) : Prop where
  creditStep : ∀ (s : Joint (ldKernel F)) (e : Fin n),
    (2 * b - 1) * dummyCost (ldKernel F) s e +
        nodeTargetCredit (ldKernel F)
          (controlledStep (ldKernel F) (ld_sealed_closed F M) s e) ≤
      targetCredit b ((ldKernel F).tgtPhase s.cfg) +
        serviceCost (ldKernel F) s e

/-- The full target-cycle package: `serviceUnique` proved, `creditStep`
assumed. -/
theorem ldTargetCycleLaws (F : BlockFrame n a b ψ) (M : MissingLDLemmas F)
    (Mc : MissingTargetCredit F M) :
    TargetCycleLaws (ldKernel F) (ld_sealed_closed F M) where
  creditStep := Mc.creditStep
  serviceUnique := ldServiceUnique F

/-! ## The redirected first-moment bound for the literal kernel -/

/-- L2b for the literal four-field kernel. -/
theorem ld_target_cycle_numerator (F : BlockFrame n a b ψ)
    (M : MissingLDLemmas F) (Mc : MissingTargetCredit F M)
    (start : Joint (ldKernel F))
    (hstart : (ldKernel F).tgtPhase start.cfg = CleanPhase.dummy 0 F.hb)
    (T : Nat) :
    (2 * b - 1) *
        edgeCostNumerator (controlledStep (ldKernel F) (ld_sealed_closed F M))
          (dummyCost (ldKernel F)) (.active start) T ≤
      edgeCostNumerator (controlledStep (ldKernel F) (ld_sealed_closed F M))
        (serviceCost (ldKernel F)) (.active start) T :=
  target_cycle_numerator (ldKernel F) (ld_sealed_closed F M)
    (ldTargetCycleLaws F M Mc) start F.hb hstart T

/-- L2c for the literal four-field kernel. -/
theorem ld_redirected_firstMoment_numerator (F : BlockFrame n a b ψ)
    (M : MissingLDLemmas F) (Mc : MissingTargetCredit F M)
    (start : Joint (ldKernel F))
    (hstart : (ldKernel F).tgtPhase start.cfg = CleanPhase.dummy 0 F.hb)
    (T : Nat) :
    n * ((2 * b - 1) *
      edgeCostNumerator (controlledStep (ldKernel F) (ld_sealed_closed F M))
        (dummyCost (ldKernel F)) (.active start) T) ≤
      truncatedActiveCostNumerator
        (controlledStep (ldKernel F) (ld_sealed_closed F M)) (.active start) T :=
  redirected_firstMoment_numerator (ldKernel F) (ld_sealed_closed F M)
    (ldTargetCycleLaws F M Mc) start F.hb hstart T

/-- The Bellman-bridged form: for the literal Algorithm-15 kernel on a
three-leader block, every natural-valued supersolution of the controlled
scheduler bounds the redirected clean-dummy firing count. -/
theorem ld_redirected_firstMoment_of_natSuper (F : BlockFrame n a b ψ)
    (M : MissingLDLemmas F) (Mc : MissingTargetCredit F M)
    (start : Joint (ldKernel F))
    (hstart : (ldKernel F).tgtPhase start.cfg = CleanPhase.dummy 0 F.hb)
    (V : StopNode (Joint (ldKernel F)) → Nat)
    (hV : NatBellmanSuperSolution
      (controlledStep (ldKernel F) (ld_sealed_closed F M)) 1 V)
    (T : Nat) :
    n * ((2 * b - 1) *
      edgeCostNumerator (controlledStep (ldKernel F) (ld_sealed_closed F M))
        (dummyCost (ldKernel F)) (.active start) T) ≤
      n ^ T * V (.active start) :=
  redirected_firstMoment_of_natSuper (ldKernel F) (ld_sealed_closed F M)
    (ldTargetCycleLaws F M Mc) start F.hb hstart V hV T

/-! ## Sanity identifications against the literal kernel -/

theorem ldKernel_rawStep (F : BlockFrame n a b ψ) :
    (ldKernel F).rawStep = ldStep F := rfl

theorem ldKernel_Lj (F : BlockFrame n a b ψ) :
    (ldKernel F).Lj = F.pos (b - 1) := rfl

theorem ldKernel_Rj (F : BlockFrame n a b ψ) :
    (ldKernel F).Rj = F.pos b := rfl

/-- `Lj` really is the edge on which the target is the responder, and `Rj` the
edge on which it is the initiator. -/
theorem ldKernel_Lj_responder (F : BlockFrame n a b ψ) :
    F.ring.rightNeighbor ((ldKernel F).Lj) = F.target := by
  have hb := F.hb
  have h : b - 1 + 1 = b := by omega
  show F.ring.rightNeighbor (F.pos (b - 1)) = F.pos b
  rw [F.rightNeighbor_pos (b - 1), h]

theorem ldKernel_Rj_initiator (F : BlockFrame n a b ψ) :
    (ldKernel F).Rj = F.target := rfl

#print axioms ldStep_pos_eq
#print axioms leaders_of_survives
#print axioms sealed_of_block_fixed
#print axioms closure_outside
#print axioms closure_leftIngress
#print axioms closure_rightEgress
#print axioms ldServiceUnique
#print axioms ld_sealed_closed
#print axioms ldTargetCycleLaws
#print axioms ld_redirected_firstMoment_of_natSuper
#print axioms ldKernel_Lj_responder

/-! ## Non-vacuity: the block frame is inhabited -/

/-- A concrete five-agent ring with three leaders at offsets `0`, `1`, `2` and
a third gap of length three. -/
def sampleFrame : BlockFrame 5 1 1 1 :=
  { ring := DirectedRing.mk (by omega)
    hpsi := by omega
    ha := by omega
    hb := by omega
    hblock := by omega
    low := 0 }


/-! ## Stall report

What is *proved* here about the literal `PPLLRepair.eliminateLeadersNoCollision`
kernel on a three-leader block:

* the `LDKernel n a b` instance itself (`ldKernel`), with every projection a
  concrete function of the four fields `(leader, bullet, shield, signal_B)`;
* `ClosureCaseLaws.outside`, `ClosureCaseLaws.leftIngress` (locality plus the
  fact that the responder leader bit is never cleared, which the stopping
  event already supplies), and `ClosureCaseLaws.rightEgress` (the attacker's
  own FIRE into a provably empty gap);
* `TargetCycleLaws.serviceUnique`.

What is *not* proved, and is assumed as `MissingLDLemmas` /
`MissingTargetCredit`:

* `atkInterior`, `tgtInterior`, `middle`, `signalProp`;
* the redirected service-count credit step.

Three obstructions found while building this instance, each of which the
assumed lemmas must absorb:

1. **No label-alignment invariant.**  `SectorSealed` constrains only bullets
   and signals.  The literal MOVE stage transports a bullet only when
   `r.label = nextLabel` and otherwise *destroys* it
   (`else (l, { r with bullet := 0 })`), and the SIGNAL stage is likewise
   guarded on alignment.  `SectorSealed` survives a destroyed bullet, but the
   credit step cannot: the sealed form must be strengthened by the repository's
   `noFreeBarrier`/`isStableIDSequence` alignment before `creditStep` is
   plausible.
2. **No bullet absorption in the base kernel.**  A dummy bullet standing next
   to a leader initiator is left in place by
   `eliminateLeadersNoCollisionMove`; absorption exists only in
   `PPLLRepair.dummyBulletSink`, used by the composed
   `PPLLCompleteMultiLeaderCleanup.eliminateLeadersNoCollisionEgressSink`.  So
   the `2nd` cleanup geometry quoted in `LDC_PROGRESS.md` is a property of the
   sink-extended kernel, not of the base Algorithm-15 repair instantiated here.
3. **FIRE and MOVE share one interaction.**  A responder dummy firing on `Lj`
   is transported in the same interaction, so `tgtPhase = dummy 0` is not the
   reachable post-firing state; see the note above `MissingTargetCredit`. -/

end LDKernelInstance
