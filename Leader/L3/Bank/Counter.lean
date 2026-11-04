import Leader.L3.Density
import Leader.L3.ProbStages

/-!
PLAN C1, deterministic first round.
No extra protocol step is introduced.
This file proves the real-role and frame infrastructure, two generic
sweep-extension lemmas, finite BANK row checks, and the strict C.1
watchdog arithmetic. It does NOT claim an authenticated reset trace
theorem or a proof of the probabilistic bank/block lemmas.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

abbrev Config (q n : Nat) := (protocol q).Configuration n

/-- Clockwise site j, with site zero the root. -/
def site {n : Nat} (ring : DirectedRing n) (r : Fin n) :
    Nat → Fin n
  | 0 => r
  | j + 1 => ring.rightNeighbor (site ring r j)

/-- The complete real PACK interval: root at zero, digits one through b.
Distinctness of these sites follows from their different PACK values. -/
def Complete {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) : Prop :=
  ∀ j : Nat, j ≤ (compileAdvice q).b →
    (C (site ring r j)).pack.val = j

/-- The only root authority guard read by BANK. -/
def GrantFree {n q : Nat} (C : Config q n) (r : Fin n) : Prop :=
  (C r).grant = false

/-- Exactly the boundary-inclusive edge support S_r in Appendix C:
the incoming edge of the root and edges at offsets zero through b. -/
def Support {n : Nat} (q : Nat) (ring : DirectedRing n)
    (r e : Fin n) : Prop :=
  ring.rightNeighbor e = r ∨
    ∃ j : Nat, j ≤ (compileAdvice q).b ∧ e = site ring r j

/-- A stronger, endpoint-based hypothesis convenient for a frame theorem.
Both endpoints are outside every site in the root--digit interval. -/
def OutsideSites {n : Nat} (q : Nat) (ring : DirectedRing n)
    (r e : Fin n) : Prop :=
  ∀ j : Nat, j ≤ (compileAdvice q).b →
    e ≠ site ring r j ∧
      ring.rightNeighbor e ≠ site ring r j

/-- A raw outward-reset location read from Agent.tok. This is NOT an
authentication of its age or provenance in arbitrary Cartesian scratch. -/
def OutwardAt {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  1 ≤ j ∧ j ≤ (compileAdvice q).b ∧
    (C (site ring r j)).tok = BTok.RR

/-- A raw leftward-reset location read from Agent.tok. -/
def LeftwardAt {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  1 ≤ j ∧ j ≤ (compileAdvice q).b ∧
    (C (site ring r j)).tok = BTok.RL

/-- All physically observable outward-token locations, in clockwise
order. The first entry is merely a leftmost candidate, not a genuine
newest-launched token without a history witness. -/
def outwardPositions {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) : List Nat :=
  ((List.range (compileAdvice q).b).map (fun i => i + 1)).filter
    (fun j => (C (site ring r j)).tok == BTok.RR)

/-- All physically observable returning-reset token locations. -/
def leftwardPositions {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) : List Nat :=
  ((List.range (compileAdvice q).b).map (fun i => i + 1)).filter
    (fun j => (C (site ring r j)).tok == BTok.RL)

/-- Outward swept prefix: both the digit bit and worker slot are clear. -/
def PrefixClear {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i → i < j →
    (C (site ring r i)).bit = false ∧
      (C (site ring r i)).tok = BTok.E

/-- Returning swept suffix: the suffix STRICTLY beyond position j
has zero bits and empty worker slots. Hence no RL remains there. -/
def SuffixClear {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  ∀ i : Nat, j < i → i ≤ (compileAdvice q).b →
    (C (site ring r i)).bit = false ∧
      (C (site ring r i)).tok = BTok.E

/-- These are physical snapshot parts of the desired trial invariant;
they do not assert that the indicated token was really launched. -/
def OutwardSnapshot {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  OutwardAt ring C r j ∧ PrefixClear ring C r j

def LeftwardSnapshot {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat) : Prop :=
  LeftwardAt ring C r j ∧ SuffixClear ring C r j

/-- One edge leaves all actual interval PACK values unchanged. -/
def RoleStableEdge {n q : Nat} (ring : DirectedRing n)
    (r : Fin n) (C : Config q n) (e : Fin n) : Prop :=
  ∀ j : Nat, j ≤ (compileAdvice q).b →
    (((protocol q).step ring C e) (site ring r j)).pack =
      (C (site ring r j)).pack

/-- The actual protocol applied successively to an edge word. -/
def Word {n q : Nat} (ring : DirectedRing n) :
    List (Fin n) → Config q n → Config q n
  | [], C => C
  | e :: w, C => Word ring w ((protocol q).step ring C e)

/-- Role stability checked at EVERY intermediate configuration. -/
def RoleStableWord {n q : Nat} (ring : DirectedRing n)
    (r : Fin n) : Config q n → List (Fin n) → Prop
  | _, [] => True
  | C, e :: w =>
      RoleStableEdge ring r C e ∧
        RoleStableWord ring r ((protocol q).step ring C e) w

/-- Grant-free at every intermediate cut, including the final cut.
Initial grant-freedom alone is not silently assumed to persist. -/
def GrantFreeWord {n q : Nat} (ring : DirectedRing n)
    (r : Fin n) : Config q n → List (Fin n) → Prop
  | C, [] => GrantFree C r
  | C, e :: w =>
      GrantFree C r ∧
        GrantFreeWord ring r ((protocol q).step ring C e) w

/-- Exact full-Agent frame lemma. It applies to transition, not to
a replacement BANK-only step. -/
theorem step_frame {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    ((protocol q).step ring C e) i = C i := by
  simp [PopulationProtocol.step, he, hj]

/-- In particular, a service with both endpoints outside S_r
cannot touch any real Agent at sites zero through b. -/
theorem outside_frame {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r e : Fin n)
    (hout : OutsideSites q ring r e) :
    ∀ j : Nat, j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring r j) =
        C (site ring r j) := by
  intro j hj
  have h := hout j hj
  exact step_frame ring C e (site ring r j)
    (Ne.symm h.1) (Ne.symm h.2)

/-- Full-Agent frame by induction over a word of unrelated services. -/
theorem word_frame {n q : Nat} (ring : DirectedRing n)
    (i : Fin n) :
    ∀ (w : List (Fin n)) (C : Config q n),
      (∀ e : Fin n, e ∈ w →
        i ≠ e ∧ i ≠ ring.rightNeighbor e) →
      (Word ring w C) i = C i := by
  intro w
  induction w with
  | nil =>
      intro C _
      rfl
  | cons e es ih =>
      intro C h
      have he : i ≠ e ∧ i ≠ ring.rightNeighbor e := by
        apply h e
        simp
      have ht : ∀ f : Fin n, f ∈ es →
          i ≠ f ∧ i ≠ ring.rightNeighbor f := by
        intro f hf
        apply h f
        simp [hf]
      calc
        (Word ring (e :: es) C) i =
            (Word ring es ((protocol q).step ring C e)) i := rfl
        _ = ((protocol q).step ring C e) i := ih _ ht
        _ = C i := step_frame ring C e i he.1 he.2

/-- Forced digit-to-digit PACK geometry from Density.goodPair. -/
theorem internal_good {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat)
    (hcomplete : Complete ring C r)
    (hj : j < (compileAdvice q).b) :
    goodPair (compileAdvice q).b
      (C (site ring r j)).pack
      (C (site ring r (j + 1))).pack = true := by
  apply (goodPair_iff _ _ _).2
  apply Or.inl
  constructor
  · have hx := hcomplete j (by omega)
    omega
  · have hx := hcomplete j (by omega)
    have hy := hcomplete (j + 1) (by omega)
    omega

/-- A selected internal good edge fixes the ENTIRE role function
under the real transition; it is not an assumed PACK step. -/
theorem internal_roles_fixed {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (r : Fin n) (j : Nat)
    (hcomplete : Complete ring C r)
    (hj : j < (compileAdvice q).b) :
    (fun i => (((protocol q).step ring C (site ring r j)) i).pack) =
      (fun i => (C i).pack) := by
  have hg := internal_good ring C r j hcomplete hj
  have hg' :
      goodPair (compileAdvice q).b
        (C (site ring r j)).pack
        (C (ring.rightNeighbor (site ring r j))).pack = true := by
    change goodPair (compileAdvice q).b
      (C (site ring r j)).pack
      (C (site ring r (j + 1))).pack = true
    exact hg
  calc
    (fun i => (((protocol q).step ring C (site ring r j)) i).pack) =
        roleWordStep (compileAdvice q).b ring
          (fun i => (C i).pack) (site ring r j) :=
      role_step ring C (site ring r j)
    _ = (fun i => (C i).pack) :=
      roleWordStep_of_good _ ring _ _ hg'

/-- A complete interval remains complete under any stipulated
role-stable word, without strengthening that stipulation. -/
theorem complete_word {n q : Nat} (ring : DirectedRing n)
    (r : Fin n) :
    ∀ (w : List (Fin n)) (C : Config q n),
      Complete ring C r →
      RoleStableWord ring r C w →
      Complete ring (Word ring w C) r := by
  intro w
  induction w with
  | nil =>
      intro C hcomplete _
      exact hcomplete
  | cons e es ih =>
      intro C hcomplete hw
      have hnext : Complete ring ((protocol q).step ring C e) r := by
        intro j hj
        rw [hw.1 j hj]
        exact hcomplete j hj
      exact ih _ hnext hw.2

/-- General word-induction interface. To instantiate it with an
authenticated worker invariant, its actual one-step hypothesis must
be discharged by case analysis on transition/bankPair. -/
theorem role_word_induction {n q : Nat} (ring : DirectedRing n)
    (r : Fin n) (I : Config q n → Prop)
    (hstep : ∀ C : Config q n, ∀ e : Fin n,
      RoleStableEdge ring r C e →
      I C → I ((protocol q).step ring C e)) :
    ∀ (w : List (Fin n)) (C : Config q n),
      RoleStableWord ring r C w → I C → I (Word ring w C) := by
  intro w
  induction w with
  | nil =>
      intro C _ hI
      exact hI
  | cons e es ih =>
      intro C hw hI
      exact ih _ hw.2 (hstep C e hw.1 hI)

/-- Pure prefix-extension arithmetic: the next digit is cleared
and all earlier digits are framed. This does not assert that the
real protocol satisfies the two premises; that is a separate row
proof. -/
theorem prefix_extend {n q : Nat} (ring : DirectedRing n)
    (C D : Config q n) (r : Fin n) (j : Nat)
    (hp : PrefixClear ring C r j)
    (hf : ∀ i : Nat, 1 ≤ i → i < j →
      (D (site ring r i)).bit = (C (site ring r i)).bit ∧
        (D (site ring r i)).tok = (C (site ring r i)).tok)
    (hn : (D (site ring r j)).bit = false ∧
      (D (site ring r j)).tok = BTok.E) :
    PrefixClear ring D r (j + 1) := by
  intro i hi hij
  by_cases hlt : i < j
  · have hprev := hp i hi hlt
    have hkeep := hf i hi hlt
    exact ⟨hkeep.1.trans hprev.1, hkeep.2.trans hprev.2⟩
  · have heq : i = j := by omega
    simpa [heq] using hn

/-- Pure suffix-retreat arithmetic, with the consumed source
cleared. Its BANK transition premise remains to be proved. -/
theorem suffix_retreat {n q : Nat} (ring : DirectedRing n)
    (C D : Config q n) (r : Fin n) (j : Nat)
    (hj : 1 ≤ j)
    (hs : SuffixClear ring C r j)
    (hf : ∀ i : Nat, j < i → i ≤ (compileAdvice q).b →
      (D (site ring r i)).bit = (C (site ring r i)).bit ∧
        (D (site ring r i)).tok = (C (site ring r i)).tok)
    (hn : (D (site ring r j)).bit = false ∧
      (D (site ring r j)).tok = BTok.E) :
    SuffixClear ring D r (j - 1) := by
  intro i hi hib
  by_cases heq : i = j
  · simpa [heq] using hn
  · have hlt : j < i := by omega
    have hprev := hs i hlt hib
    have hkeep := hf i hlt hib
    exact ⟨hkeep.1.trans hprev.1, hkeep.2.trans hprev.2⟩

/-! Closed row sanity checks on the literal BANK owner. These
are finite evaluations, not replacements for a parametric sweep
proof or for an end-to-end transition projection lemma. -/

private def rowCell (role : Nat) (bit : Bool) (tok : BTok) : BankCell :=
  { role := role, mode := .RESET, bit := bit, tok := tok,
    lease := 0, grant := false }

theorem sample_launch_overwrites :
    let z := bankPair (rowCell 0 false .E)
      (rowCell 1 true .IR) 1 18 (fun _ => false)
    z.1.mode = .RWAIT ∧ z.2.bit = false ∧ z.2.tok = .RR := by
  decide

theorem sample_outward_overwrites :
    let z := bankPair (rowCell 4 false .RR)
      (rowCell 5 true .CL1) 5 18 (fun _ => false)
    z.1.tok = .E ∧ z.2.bit = false ∧ z.2.tok = .RR := by
  decide

theorem sample_top_turn :
    let z := bankPair (rowCell 17 false .E)
      (rowCell 18 false .RR) 18 18 (fun _ => false)
    z.1.bit = false ∧ z.1.tok = .RL ∧ z.2.tok = .E := by
  decide

theorem sample_leftward_overwrites :
    let z := bankPair (rowCell 9 true .IR)
      (rowCell 10 false .RL) 10 18 (fun _ => false)
    z.1.bit = false ∧ z.1.tok = .RL ∧ z.2.tok = .E := by
  decide

private def rawRootCell : BankCell :=
  { role := 0, mode := .RWAIT, bit := false, tok := .E,
    lease := 0, grant := false }

private def rawFirstCell : BankCell :=
  { role := 1, mode := .RESET, bit := false, tok := .RL,
    lease := 0, grant := false }

/-- A raw RL in arbitrary scratch is accepted. This is exactly why
a returning token is not automatically an authenticated sweep. -/
theorem raw_rl_arms :
    let z := bankPair rawRootCell rawFirstCell 1 18 (fun _ => false)
    z.1.mode = .ARMED ∧ z.2.tok = .E := by
  decide

/-- The corresponding real Cartesian Agent pair for the q=80
spatial compilation. All unspecified fields are Agent.blank. -/
def rawRootAgent : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with mode := .RWAIT }

def rawFirstAgent : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with
    pack := ⟨1, by decide⟩, tok := .RL }

/-- A possible unserviced second digit, with a dirty bit. -/
def rawSecondAgent : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with
    pack := ⟨2, by decide⟩, bit := true }

/-! Exact watchdog arithmetic (C.1). The next three lemmas prove a
strictly stronger estimate than delta_b < 1/2, for ALL b >= 0. -/

private def watchdogNum (b : Nat) : Nat :=
  2 ^ (2 * b + 3) * 4 ^ (11 * b + 24)

private def watchdogDen (b : Nat) : Nat :=
  5 ^ (11 * b + 24)

private theorem watchdog_num_succ (b : Nat) :
    watchdogNum (b + 1) =
      watchdogNum b * (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) := by
  have htwo : 2 * (b + 1) + 3 = (2 * b + 3) + 2 := by omega
  have hfour : 11 * (b + 1) + 24 = (11 * b + 24) + 11 := by omega
  unfold watchdogNum
  rw [htwo, hfour, Nat.pow_add 2 (2 * b + 3) 2, Nat.pow_add 4 (11 * b + 24) 11]
  generalize 2 ^ (2 * b + 3) = A
  generalize 4 ^ (11 * b + 24) = B
  generalize (2 : Nat) ^ (2 : Nat) = C
  generalize (4 : Nat) ^ (11 : Nat) = D
  rw [Nat.mul_assoc A C, Nat.mul_assoc A B, Nat.mul_left_comm C B D]

private theorem watchdog_den_succ (b : Nat) :
    watchdogDen (b + 1) = watchdogDen b * 5 ^ (11 : Nat) := by
  have hfive : 11 * (b + 1) + 24 = (11 * b + 24) + 11 := by omega
  unfold watchdogDen
  rw [hfive, Nat.pow_add]

private theorem watchdog_num_lt_den :
    ∀ b : Nat, watchdogNum b < watchdogDen b := by
  intro b
  induction b with
  | zero =>
      decide +kernel
  | succ b ih =>
      have hfactor :
          2 ^ (2 : Nat) * 4 ^ (11 : Nat) < 5 ^ (11 : Nat) := by
        decide
      have hpos :
          0 < 2 ^ (2 : Nat) * 4 ^ (11 : Nat) := by
        decide
      have hden : 0 < watchdogDen b :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) ih
      have ha :
          watchdogNum b * (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) <
            watchdogDen b * (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) :=
        Nat.mul_lt_mul_of_pos_right ih hpos
      have hb :
          watchdogDen b * (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) <
            watchdogDen b * 5 ^ (11 : Nat) :=
        Nat.mul_lt_mul_of_pos_left hfactor hden
      calc
        watchdogNum (Nat.succ b) =
            watchdogNum b * (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) := by
          simpa only [Nat.succ_eq_add_one] using watchdog_num_succ b
        _ < watchdogDen b *
              (2 ^ (2 : Nat) * 4 ^ (11 : Nat)) := ha
        _ < watchdogDen b * 5 ^ (11 : Nat) := hb
        _ = watchdogDen (Nat.succ b) := by
          simpa only [Nat.succ_eq_add_one] using
            (watchdog_den_succ b).symm

/-- Strong C.1: twice the numerator is strictly below the
denominator. Thus the failure bound delta_b is < 1/2.
This holds even at b=0, hence at every requested b >= 1. -/
theorem watchdog_half (b : Nat) :
    2 * (2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) <
      5 ^ (11 * b + 24) := by
  have he : 2 * b + 3 = (2 * b + 2) + 1 := by omega
  have hp : 2 ^ (2 * b + 3) = 2 * 2 ^ (2 * b + 2) := by
    rw [he, Nat.pow_succ]
    ac_rfl
  calc
    2 * (2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) =
        watchdogNum b := by
      unfold watchdogNum
      rw [hp]
      ac_rfl
    _ < watchdogDen b := watchdog_num_lt_den b
    _ = 5 ^ (11 * b + 24) := rfl

/-- The strict inequality in the unscaled form of (C.1). -/
theorem watchdog_strict (b : Nat) :
    2 ^ (2 * b + 2) * 4 ^ (11 * b + 24) <
      5 ^ (11 * b + 24) := by
  have h := watchdog_half b
  omega

end Counter
end L3


/-! ## Ghost generations for BANK reset workers

Every ghost transition projects to the ORIGINAL physical protocol.
The label is proof-only and does not authenticate arbitrary inherited RL
bytes. The row-lift and complete word-preservation obligations are
kept distinct from the exact ghost bookkeeping.
-/

namespace L3
namespace Counter

attribute [local instance low] Classical.propDecidable

/-- Fresh reset generation of a worker (RR or RL). None means either
an inherited/unproved worker or an absent worker: neither is
authenticated. New generations use the ghost's monotonically
increasing service clock. -/
abbrev ResetGeneration := Option Nat

/-- The only genuine origin of an RR generation: an unchanged
role-zero to role-one edge, grant-free, in RESET mode, in the
spatial (not SMALL) implementation. Every conjunct is an OLD
field/role guard of bankPair. -/
def resetLaunchGuard {c : Compiled}
    (x y : Agent c) : Bool :=
  decide (c.useSmall = false ∧
    x.pack.val = 0 ∧ x.grant = false ∧ x.mode = .RESET ∧
    y.pack.val = 1 ∧
    packNext x.pack.val y.pack.val c.b = 1)

/-- A reset worker at an interior digit is transported clockwise.
The source RR priority dominates a resident RL or RR. -/
def resetForwardGuard {c : Compiled}
    (x y : Agent c) : Bool :=
  decide (c.useSmall = false ∧
    1 ≤ x.pack.val ∧ x.pack.val < c.b ∧
    y.pack.val = x.pack.val + 1 ∧
    packNext x.pack.val y.pack.val c.b = y.pack.val ∧
    x.tok = .RR)

/-- A rightmost RR turns left when the selected source has no RR.
The source-RR priority must be checked before the top turn. -/
def resetTurnGuard {c : Compiled}
    (x y : Agent c) : Bool :=
  decide (c.useSmall = false ∧
    1 ≤ x.pack.val ∧ x.pack.val < c.b ∧
    y.pack.val = x.pack.val + 1 ∧
    packNext x.pack.val y.pack.val c.b = y.pack.val ∧
    x.tok ≠ .RR ∧ y.pack.val = c.b ∧ y.tok = .RR)

/-- A leftward RL overwrites the destination worker and clears
the old source, unless an outward RR at x takes priority. -/
def resetRetreatGuard {c : Compiled}
    (x y : Agent c) : Bool :=
  decide (c.useSmall = false ∧
    1 ≤ x.pack.val ∧ x.pack.val < c.b ∧
    y.pack.val = x.pack.val + 1 ∧
    packNext x.pack.val y.pack.val c.b = y.pack.val ∧
    x.tok ≠ .RR ∧ y.tok = .RL)

/-- A generation tag is retained only if the PHYSICAL worker slot
is RR or RL after the selected transition. Other workers cannot
inherit a reset generation by coincidence. -/
def resetScreen (actual : BTok) (tag : ResetGeneration) :
    ResetGeneration :=
  if actual == .RR || actual == .RL then tag else none

theorem reset_screen_sound (actual : BTok) (tag : ResetGeneration)
    (gen : Nat) (h : resetScreen actual tag = some gen) :
    actual = .RR ∨ actual = .RL := by
  cases actual <;> simp [resetScreen] at h ⊢

theorem reset_screen_empty (tag : ResetGeneration) :
    resetScreen .E tag = none := by
  rfl

/-- BANK ghost arbiter, after the full REAL transition has written
the two endpoint slots. All priorities follow the old bankPair:
genuine launch, source RR, terminal RR turn, incoming RL, and
otherwise same-slot preservation. A changed physical token loses
its tag. In particular a resident overwritten by a newer RR never
donates its old tag to that new RR. -/
def resetTagPair {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (tagX tagY : ResetGeneration) (stamp : Nat) :
    ResetGeneration × ResetGeneration :=
  let launch := resetLaunchGuard oldX oldY
  let outward := resetForwardGuard oldX oldY
  let top := resetTurnGuard oldX oldY
  let back := resetRetreatGuard oldX oldY
  let intoX : ResetGeneration :=
    if newX.tok == .RL then
      if top || back then tagY
      else if oldX.tok == .RL then tagX
      else none
    else if newX.tok == .RR then
      if oldX.tok == .RR then tagX else none
    else none
  let intoY : ResetGeneration :=
    if newY.tok == .RR then
      if launch then some stamp
      else if outward then tagX
      else if oldY.tok == .RR then tagY
      else none
    else if newY.tok == .RL then
      if oldY.tok == .RR || oldY.tok == .RL then tagY
      else none
    else none
  (resetScreen newX.tok intoX, resetScreen newY.tok intoY)

/-- A successful (real) launch has a fresh, not inherited, token
generation at the responder. No initial RL can satisfy this event. -/
theorem reset_tag_pair_launch {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp : Nat)
    (hlaunch : resetLaunchGuard oldX oldY = true)
    (htok : newY.tok = .RR) :
    (resetTagPair oldX oldY newX newY markX markY stamp).2 =
      some stamp := by
  simp [resetTagPair, resetScreen, hlaunch, htok]

/-- The source RR wins and donates its own generation to the new
RR responder, even when the responder held an older return. -/
theorem reset_tag_pair_outward {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp : Nat)
    (hnot : resetLaunchGuard oldX oldY = false)
    (hout : resetForwardGuard oldX oldY = true)
    (htok : newY.tok = .RR) :
    (resetTagPair oldX oldY newX newY markX markY stamp).2 =
      markX := by
  simp [resetTagPair, resetScreen, hnot, hout, htok]

/-- Top turn or retreat takes the generation of the OLD right
responder, never of an overwritten resident at the left. -/
theorem reset_tag_pair_leftward {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp : Nat)
    (hleft : resetTurnGuard oldX oldY = true ∨
      resetRetreatGuard oldX oldY = true)
    (htok : newX.tok = .RL) :
    (resetTagPair oldX oldY newX newY markX markY stamp).1 =
      markY := by
  have hor : (resetTurnGuard oldX oldY ||
      resetRetreatGuard oldX oldY) = true := by
    rcases hleft with h | h
    · simp [h]
    · simp [h]
  simp [resetTagPair, resetScreen, htok, hor]

/-- Physical erasure of both reset slots erases BOTH proof tags.
This is the precise overwrite rule, not a ghost-only deletion. -/
theorem reset_tag_pair_overwritten {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp : Nat)
    (hx : newX.tok = .E) (hy : newY.tok = .E) :
    resetTagPair oldX oldY newX newY markX markY stamp =
      (none, none) := by
  simp [resetTagPair, resetScreen, hx, hy]

theorem reset_tag_pair_source_sound {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp gen : Nat)
    (h : (resetTagPair oldX oldY newX newY
      markX markY stamp).1 = some gen) :
    newX.tok = .RR ∨ newX.tok = .RL := by
  exact reset_screen_sound newX.tok _ gen h

theorem reset_tag_pair_target_sound {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (markX markY : ResetGeneration) (stamp gen : Nat)
    (h : (resetTagPair oldX oldY newX newY
      markX markY stamp).2 = some gen) :
    newY.tok = .RR ∨ newY.tok = .RL := by
  exact reset_screen_sound newY.tok _ gen h

/-- Only a root in physical RWAIT can retain an authenticated
root wait. A fresh launch binds it to that same service stamp;
an unchanged RWAIT carries its prior tag, while timeout or
successful return clears it. -/
def resetWaitPair {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (waitX waitY : ResetGeneration) (stamp : Nat) :
    ResetGeneration × ResetGeneration :=
  let source :=
    if newX.pack.val = 0 ∧ newX.mode = .RWAIT then
      if resetLaunchGuard oldX oldY then some stamp
      else if oldX.mode = .RWAIT then waitX else none
    else none
  let target :=
    if newY.pack.val = 0 ∧ newY.mode = .RWAIT then
      if oldY.mode = .RWAIT then waitY else none
    else none
  (source, target)

theorem reset_wait_source_sound {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (waitX waitY : ResetGeneration) (stamp gen : Nat)
    (h : (resetWaitPair oldX oldY newX newY
      waitX waitY stamp).1 = some gen) :
    newX.pack.val = 0 ∧ newX.mode = .RWAIT := by
  by_cases hguard : newX.pack.val = 0 ∧ newX.mode = .RWAIT
  · exact hguard
  · exfalso
    have h' : (resetWaitPair oldX oldY newX newY
        waitX waitY stamp).1 = none := by
      show (if newX.pack.val = 0 ∧ newX.mode = .RWAIT then _ else none) = none
      exact if_neg hguard
    rw [h'] at h
    cases h

theorem reset_wait_target_sound {c : Compiled}
    (oldX oldY newX newY : Agent c)
    (waitX waitY : ResetGeneration) (stamp gen : Nat)
    (h : (resetWaitPair oldX oldY newX newY
      waitX waitY stamp).2 = some gen) :
    newY.pack.val = 0 ∧ newY.mode = .RWAIT := by
  by_cases hguard : newY.pack.val = 0 ∧ newY.mode = .RWAIT
  · exact hguard
  · exfalso
    have h' : (resetWaitPair oldX oldY newX newY
        waitX waitY stamp).2 = none := by
      show (if newY.pack.val = 0 ∧ newY.mode = .RWAIT then _ else none) = none
      exact if_neg hguard
    rw [h'] at h
    cases h

/-- Exact product state: the original full Cartesian configuration
plus only proof-only root-wait and RR/RL-generation histories.
The last-launch label is retained after timeout, so an abandoned
worker is never silently upgraded when it returns later. -/
structure ResetGhost (n q : Nat) where
  physical : Config q n
  marks : Fin n → ResetGeneration
  waits : Fin n → ResetGeneration
  lastLaunch : Fin n → ResetGeneration
  clock : Nat

/-- Inherited arbitrary BANK scratch has no authenticated launch.
One is not allowed to infer provenance from a matching token byte. -/
def resetGhostInit {n q : Nat} (C : Config q n) (cut : Nat) :
    ResetGhost n q :=
  { physical := C
    marks := fun _ => none
    waits := fun _ => none
    lastLaunch := fun _ => none
    clock := cut }

/-- One physical service of the ACTUAL protocol q; the shadow tags
are computed from the old and actual new selected endpoints only.
Every other ghost mark is framed. -/
def resetGhostStep {n q : Nat}
    (ring : DirectedRing n)
    (G : ResetGhost n q) (e : Fin n) : ResetGhost n q :=
  let y := ring.rightNeighbor e
  let C' := (protocol q).step ring G.physical e
  let stamp := G.clock + 1
  let xOld := G.physical e
  let yOld := G.physical y
  let xNew := C' e
  let yNew := C' y
  let tags := resetTagPair xOld yOld xNew yNew
    (G.marks e) (G.marks y) stamp
  let waits := resetWaitPair xOld yOld xNew yNew
    (G.waits e) (G.waits y) stamp
  let launch := resetLaunchGuard xOld yOld && xNew.mode == .RWAIT &&
    yNew.tok == .RR
  { physical := C'
    marks := fun i =>
      if i = e then tags.1
      else if i = y then tags.2
      else G.marks i
    waits := fun i =>
      if i = e then waits.1
      else if i = y then waits.2
      else G.waits i
    lastLaunch := fun i =>
      if i = e && launch then some stamp else G.lastLaunch i
    clock := stamp }

/-- The FreshScan-style exact projection theorem, for every current
ghost state and every raw edge. No frozen sector or reachable-state
assumption is needed for equality of the physical coordinates. -/
theorem resetGhost_projection {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q) (e : Fin n) :
    (resetGhostStep ring G e).physical =
      (protocol q).step ring G.physical e := by
  rfl

theorem resetGhost_initial_projection {n q : Nat}
    (C : Config q n) (cut : Nat) :
    (resetGhostInit C cut).physical = C := by
  rfl

theorem resetGhost_clock_step {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q) (e : Fin n) :
    (resetGhostStep ring G e).clock = G.clock + 1 := by
  rfl

theorem resetGhost_initial_untrusted {n q : Nat}
    (C : Config q n) (cut : Nat) (i : Fin n) :
    (resetGhostInit C cut).marks i = none ∧
    (resetGhostInit C cut).waits i = none ∧
    (resetGhostInit C cut).lastLaunch i = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- Nonincident agents retain exactly their old proof-only stamps. -/
theorem resetGhost_nonincident_frame {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (e i : Fin n) (hi : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    (resetGhostStep ring G e).marks i = G.marks i ∧
    (resetGhostStep ring G e).waits i = G.waits i ∧
    (resetGhostStep ring G e).lastLaunch i = G.lastLaunch i := by
  simp [resetGhostStep, hi, hj, Ne.symm hi]

/-- Physical tagged-worker soundness. An attached generation must
be on an actual RR/RL worker, not just an arbitrary stored byte. -/
def ResetGhostMarkSound {n q : Nat} (G : ResetGhost n q) : Prop :=
  ∀ i gen, G.marks i = some gen →
    (G.physical i).tok = .RR ∨ (G.physical i).tok = .RL

theorem resetGhost_init_mark_sound {n q : Nat}
    (C : Config q n) (cut : Nat) :
    ResetGhostMarkSound (resetGhostInit C cut) := by
  intro i gen h
  cases h

/-- The checker for one edge depends only on the two actual written
slots and preserves all nonincident sound marks by physical framing. -/
theorem resetGhost_marks_eq {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q) (e i : Fin n) :
    (resetGhostStep ring G e).marks i =
      if i = e then
        (resetTagPair (G.physical e) (G.physical (ring.rightNeighbor e))
          ((protocol q).step ring G.physical e e)
          ((protocol q).step ring G.physical e (ring.rightNeighbor e))
          (G.marks e) (G.marks (ring.rightNeighbor e)) (G.clock + 1)).1
      else if i = ring.rightNeighbor e then
        (resetTagPair (G.physical e) (G.physical (ring.rightNeighbor e))
          ((protocol q).step ring G.physical e e)
          ((protocol q).step ring G.physical e (ring.rightNeighbor e))
          (G.marks e) (G.marks (ring.rightNeighbor e)) (G.clock + 1)).2
      else G.marks i := rfl

theorem resetGhost_mark_sound_step {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (e : Fin n)
    (hs : ResetGhostMarkSound G) :
    ResetGhostMarkSound (resetGhostStep ring G e) := by
  intro i gen h
  rw [resetGhost_marks_eq] at h
  by_cases hi : i = e
  · subst i
    rw [if_pos rfl] at h
    exact reset_tag_pair_source_sound _ _ _ _ _ _ _ _ h
  · rw [if_neg hi] at h
    by_cases hj : i = ring.rightNeighbor e
    · subst hj
      rw [if_pos rfl] at h
      exact reset_tag_pair_target_sound _ _ _ _ _ _ _ _ h
    · rw [if_neg hj] at h
      have old := hs i gen h
      have hframe : (protocol q).step ring G.physical e i = G.physical i :=
        step_frame ring G.physical e i hi hj
      rw [resetGhost_projection, hframe]
      exact old

/-- A finite ghost path uses the same raw scheduler word. -/
def resetGhostWord {n q : Nat}
    (ring : DirectedRing n) :
    List (Fin n) → ResetGhost n q → ResetGhost n q
  | [], G => G
  | e :: es, G => resetGhostWord ring es (resetGhostStep ring G e)

theorem resetGhost_word_projection {n q : Nat}
    (ring : DirectedRing n) (w : List (Fin n))
    (G : ResetGhost n q) :
    (resetGhostWord ring w G).physical =
      Word ring w G.physical := by
  induction w generalizing G with
  | nil => rfl
  | cons e es ih =>
      change (resetGhostWord ring es (resetGhostStep ring G e)).physical =
        Word ring es ((protocol q).step ring G.physical e)
      rw [ih]
      rfl

/-- The complete-domain induction interface, now on actual ghost
paths instead of token snapshots. Its one-step premise is explicit;
it does not assert the still-unproved BANK sweep property. -/
theorem resetGhost_role_word_induction {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (I : ResetGhost n q → Prop)
    (hstep : ∀ G e, RoleStableEdge ring root G.physical e →
      I G → I (resetGhostStep ring G e)) :
    ∀ (w : List (Fin n)) (G : ResetGhost n q),
      RoleStableWord ring root G.physical w →
      I G → I (resetGhostWord ring w G) := by
  intro w
  induction w with
  | nil =>
      intro G _ hG
      exact hG
  | cons e es ih =>
      intro G hw hG
      have hwNext : RoleStableWord ring root
          (resetGhostStep ring G e).physical es := by
        simpa only [resetGhost_projection] using hw.2
      exact ih (resetGhostStep ring G e) hwNext
        (hstep G e hw.1 hG)

/-- Sound marking persists under all raw words, even when the
intermediate PACK roles are not stable. Role stability is needed
only for the stronger swept-prefix and swept-suffix assertions. -/
theorem resetGhost_word_mark_sound {n q : Nat}
    (ring : DirectedRing n)
    (w : List (Fin n)) (G : ResetGhost n q)
    (h : ResetGhostMarkSound G) :
    ResetGhostMarkSound (resetGhostWord ring w G) := by
  induction w generalizing G with
  | nil => exact h
  | cons e es ih =>
      exact ih (resetGhostStep ring G e)
        (resetGhost_mark_sound_step ring G e h)

/-- A root's latest generation is keyed by launch history rather
than inferred from the returning token byte. -/
def ResetNewestOutward {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (root : Fin n) (j : Nat) : Prop :=
  ∃ gen,
    G.lastLaunch root = some gen ∧
    G.marks (site ring root j) = some gen ∧
    (G.physical (site ring root j)).tok = .RR

def ResetNewestLeftward {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (root : Fin n) (j : Nat) : Prop :=
  ∃ gen,
    G.lastLaunch root = some gen ∧
    G.marks (site ring root j) = some gen ∧
    (G.physical (site ring root j)).tok = .RL

/-- The target proof of Appendix C(c): authenticated current
outward workers must have a swept prefix; current leftward workers
must have a swept suffix. This is a DEFINITION, not a theorem
pretending that its row induction has been discharged. -/
def ResetNewestSweepSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) : Prop :=
  (∀ j, ResetNewestOutward ring G root j →
    PrefixClear ring G.physical root j) ∧
  (∀ j, ResetNewestLeftward ring G root j →
    SuffixClear ring G.physical root j)

/-- The initial arbitrary Cartesian scratch has no generations and
therefore satisfies the sweep certificate vacuously. -/
theorem resetGhost_init_sweep_sound {n q : Nat}
    (ring : DirectedRing n)
    (C : Config q n) (cut : Nat) (root : Fin n) :
    ResetNewestSweepSound ring root (resetGhostInit C cut) := by
  constructor
  · intro j h
    obtain ⟨gen, hlast, _, _⟩ := h
    cases hlast
  · intro j h
    obtain ⟨gen, hlast, _, _⟩ := h
    cases hlast

end Counter
end L3
/-! ## Literal BANK counterexamples to the requested partition

It records two obstructions to the requested
strong statements rather than adding a false preservation theorem.

1. The complement of the four RESET guards is NOT BANK stuttering:
   an ARMED root can set the first digit bit to true.
2. ResetNewestSweepSound quantifies over every Nat position. A site
   beyond one full ring aliases a real digit, making its PrefixClear
   conjunct contradict the actual newest RR. This is a definition
   defect, not evidence that the physical Appendix C reset sweep fails.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-! ### The real, no-reset-guard ARMED row -/

/-- The source at a role-zero root is grant-free but ARMED. -/
private def resetArmedRoot : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with mode := .ARMED }

/-- Ordinary role-one digit with empty worker and zero bit. -/
private def resetArmedDigit : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with pack := ⟨1, by decide +kernel⟩ }

/-- Exact finite witness through Protocol.transition, including the
real Base.bankPair, not a substitute transition. None of the four
reset guards holds; the ARMED root nevertheless writes bit=true.
Thus an unqualified "no reset guard -> unchanged or only cleared"
branch is false for the full Cartesian BANK state. -/
theorem reset_no_guard_armed_writes :
    resetLaunchGuard resetArmedRoot resetArmedDigit = false ∧
    resetForwardGuard resetArmedRoot resetArmedDigit = false ∧
    resetTurnGuard resetArmedRoot resetArmedDigit = false ∧
    resetRetreatGuard resetArmedRoot resetArmedDigit = false ∧
    (transition (compileAdvice 80)
       resetArmedRoot resetArmedDigit).1.mode = .CSTART ∧
    (transition (compileAdvice 80)
       resetArmedRoot resetArmedDigit).2.bit = true := by
  decide +kernel

/-! ### The unbounded-index alias in ResetNewestSweepSound -/

/-- This is independent of how a physical RR was created: if a
newest RR occupies position i, and position j>i aliases it,
the unbounded PrefixClear at j requires that very RR to be E.
It proves *negation*, rather than a weakened sweep assertion. -/
theorem reset_newest_outward_alias_obstruction {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) (i j : Nat)
    (hi : 1 ≤ i) (hij : i < j)
    (halias : site ring root j = site ring root i)
    (hfront : ResetNewestOutward ring G root i) :
    ¬ ResetNewestSweepSound ring root G := by
  intro hs
  obtain ⟨gen, hlast, hmark, htok⟩ := hfront
  have hfrontAtAlias : ResetNewestOutward ring G root j := by
    refine ⟨gen, hlast, ?_, ?_⟩
    · simpa only [halias] using hmark
    · simpa only [halias] using htok
  have hclear := (hs.1 j hfrontAtAlias) i hi hij
  rw [hclear.2] at htok
  cases htok

/-- A ring with twenty physical edges: the spatial q=80 BANK
compilation has width b=18, so the root/digits fit. -/
private def resetAliasRing : DirectedRing 20 :=
  ⟨by decide⟩

private theorem resetExampleWidth :
    (compileAdvice 80).b + 2 = 20 := by
  decide +kernel

/-- A real complete role interval, with all other local coordinates
initially blank. Site 0 has role zero; site i has role i. -/
private def resetExampleConfig : Config 80 20 :=
  fun i =>
    { Agent.blank (compileAdvice 80) with
      pack := ⟨i.val, by
        have h : i.val < 20 := i.isLt
        simpa only [resetExampleWidth] using h⟩ }

private theorem resetExampleSiteVal :
    ∀ j : Nat, j < 20 →
      (site resetAliasRing (0 : Fin 20) j).val = j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      change (((site resetAliasRing (0 : Fin 20) j).val + 1) % 20) = j + 1
      rw [ih (by omega)]
      exact Nat.mod_eq_of_lt hj

private theorem resetExampleComplete :
    Complete resetAliasRing resetExampleConfig (0 : Fin 20) := by
  intro j hj
  have hjlt : j < 20 := by
    have hw := resetExampleWidth
    omega
  change (site resetAliasRing (0 : Fin 20) j).val = j
  exact resetExampleSiteVal j hjlt

private theorem resetExampleGrantFree :
    GrantFree resetExampleConfig (0 : Fin 20) := by
  rfl

private theorem resetExampleRoleStable :
    RoleStableEdge resetAliasRing (0 : Fin 20)
      resetExampleConfig (0 : Fin 20) := by
  have hroles :=
    internal_roles_fixed resetAliasRing resetExampleConfig
      (0 : Fin 20) 0 resetExampleComplete
      (by decide +kernel : 0 < (compileAdvice 80).b)
  intro j _
  exact congrFun hroles (site resetAliasRing (0 : Fin 20) j)

private theorem resetExampleWordStable :
    RoleStableWord resetAliasRing (0 : Fin 20)
      resetExampleConfig [(0 : Fin 20)] := by
  exact ⟨resetExampleRoleStable, trivial⟩

private theorem resetExampleEdgeInSupport :
    Support 80 resetAliasRing (0 : Fin 20) (0 : Fin 20) := by
  exact Or.inr ⟨0, by decide +kernel, rfl⟩

/-- Serve precisely the actual edge 0->1 once after resetGhostInit.
The source has pack=0, mode=RESET, grant=false; the responder has
pack=1, bit=false, tok=E. BANK launches RR, zeros bit, and enters RWAIT.
The ghost correctly labels that physical launch stamp 1. -/
private def resetExampleAfter : ResetGhost 20 80 :=
  resetGhostStep resetAliasRing
    (resetGhostInit resetExampleConfig 0) (0 : Fin 20)

private theorem resetExampleFront :
    ResetNewestOutward resetAliasRing resetExampleAfter
      (0 : Fin 20) 1 := by
  refine ⟨1, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Exactly one full physical lap aliases the newest digit-one
front: site(21)=site(1) in the twenty-site example. -/
private theorem resetExampleAlias :
    site resetAliasRing (0 : Fin 20) 21 =
      site resetAliasRing (0 : Fin 20) 1 := by
  decide +kernel

/-- This is the requested newest-sweep assertion's exact negation
after an actual launch. Position 21 satisfies ResetNewestOutward
as written, while PrefixClear at 21 requires digit one to be E.
Digit one is the authenticated RR. -/
theorem reset_newest_sweep_false_after_launch :
    ¬ ResetNewestSweepSound resetAliasRing (0 : Fin 20)
      resetExampleAfter := by
  exact reset_newest_outward_alias_obstruction
    resetAliasRing (0 : Fin 20) resetExampleAfter 1 21
    (by decide) (by decide) resetExampleAlias resetExampleFront

/-- Fully scoped word counterexample: complete BANK interval,
grant-free root, role-stable chosen edge inside the support, and
a genuine launched generation. Consequently the requested
universal word induction instantiated with ResetNewestSweepSound
is false for the exact definition currently in Counter.lean. -/
theorem reset_newest_role_word_universal_false :
    ∃ (C : Config 80 20) (w : List (Fin 20)),
      Complete resetAliasRing C (0 : Fin 20) ∧
      GrantFree C (0 : Fin 20) ∧
      RoleStableWord resetAliasRing (0 : Fin 20) C w ∧
      (∀ e : Fin 20, e ∈ w →
        Support 80 resetAliasRing (0 : Fin 20) e) ∧
      ¬ ResetNewestSweepSound resetAliasRing (0 : Fin 20)
        (resetGhostWord resetAliasRing w (resetGhostInit C 0)) := by
  refine ⟨resetExampleConfig, [(0 : Fin 20)],
    resetExampleComplete, resetExampleGrantFree,
    resetExampleWordStable, ?_, ?_⟩
  · intro e he
    have heq : e = (0 : Fin 20) := by
      simpa only [List.mem_singleton] using he
    subst e
    exact resetExampleEdgeInSupport
  · change ¬ ResetNewestSweepSound resetAliasRing (0 : Fin 20)
      resetExampleAfter
    exact reset_newest_sweep_false_after_launch

end Counter
end L3



/-! ## Bounded reset positions and the literal BANK complement

A finite position is a digit in 0..b, with zero
excluded from the worker-front predicates. A ghost label is not a
reachability certificate; root-mode coherence remains a separate
historical obligation.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- Finite version of Complete, covering the root and all b digits. -/
def ResetFiniteComplete {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (root : Fin n) : Prop :=
  ∀ j : Fin ((compileAdvice q).b + 1),
    (C (site ring root j.val)).pack.val = j.val

theorem resetCompleteIffFinite {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n) :
    Complete ring C root ↔ ResetFiniteComplete ring C root := by
  constructor
  · intro hc j
    exact hc j.val (by omega)
  · intro hf j hj
    exact hf ⟨j, by omega⟩

/-- Finite equivalent of the selected-edge role-stability premise. -/
def ResetFiniteRoleStable {n q : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config q n) (e : Fin n) : Prop :=
  ∀ j : Fin ((compileAdvice q).b + 1),
    (((protocol q).step ring C e) (site ring root j.val)).pack =
      (C (site ring root j.val)).pack

theorem resetRoleStableIffFinite {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) :
    RoleStableEdge ring root C e ↔
      ResetFiniteRoleStable ring root C e := by
  constructor
  · intro hs j
    exact hs j.val (by omega)
  · intro hf j hj
    exact hf ⟨j, by omega⟩

/-- Completeness prevents aliasing between two finite role indices. -/
theorem resetFiniteSitesInjective {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n)
    (hc : Complete ring C root)
    (i j : Fin ((compileAdvice q).b + 1))
    (heq : site ring root i.val = site ring root j.val) :
    i = j := by
  apply Fin.ext
  have hi := hc i.val (by omega)
  have hj := hc j.val (by omega)
  rw [heq] at hi
  omega

/-- Authentication of one outward worker at a finite digit, not an
unbounded Nat representative of the same physical site. -/
def ResetOutwardDigit {n q : Nat} (ring : DirectedRing n)
    (G : ResetGhost n q) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) : Prop :=
  0 < j.val ∧
    (G.lastLaunch root).isSome = true ∧
    G.marks (site ring root j.val) = G.lastLaunch root ∧
    (G.physical (site ring root j.val)).tok = .RR

def ResetLeftwardDigit {n q : Nat} (ring : DirectedRing n)
    (G : ResetGhost n q) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) : Prop :=
  0 < j.val ∧
    (G.lastLaunch root).isSome = true ∧
    G.marks (site ring root j.val) = G.lastLaunch root ∧
    (G.physical (site ring root j.val)).tok = .RL

/-- The prefix and suffix quantify only over physical digit slots. -/
def ResetPrefixDigit {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) : Prop :=
  ∀ i : Fin ((compileAdvice q).b + 1),
    0 < i.val → i.val < j.val →
    (C (site ring root i.val)).bit = false ∧
      (C (site ring root i.val)).tok = .E

def ResetSuffixDigit {n q : Nat} (ring : DirectedRing n)
    (C : Config q n) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) : Prop :=
  ∀ i : Fin ((compileAdvice q).b + 1),
    j.val < i.val →
    (C (site ring root i.val)).bit = false ∧
      (C (site ring root i.val)).tok = .E

/-- The repaired snapshot (the original unrestricted predicate above
remains as a historical negative test). The new binder has b+1
inhabitants, so offset i+n cannot re-enter as a different digit. -/
def ResetNewestSweepBounded {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) : Prop :=
  (∀ j : Fin ((compileAdvice q).b + 1),
    ResetOutwardDigit ring G root j →
      ResetPrefixDigit ring G.physical root j) ∧
  (∀ j : Fin ((compileAdvice q).b + 1),
    ResetLeftwardDigit ring G root j →
      ResetSuffixDigit ring G.physical root j)

/-- Within the bounded domain the repaired prefix is exactly the
original PrefixClear, which already had the restriction i < j. -/
theorem resetPrefixDigitIffOld {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) :
    ResetPrefixDigit ring C root j ↔
      PrefixClear ring C root j.val := by
  constructor
  · intro h i hi hij
    have hjbound : j.val < (compileAdvice q).b + 1 := j.isLt
    exact h ⟨i, by omega⟩ (by show 0 < i; omega) hij
  · intro h i hi hij
    exact h i.val (by omega) hij

theorem resetSuffixDigitIffOld {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1)) :
    ResetSuffixDigit ring C root j ↔
      SuffixClear ring C root j.val := by
  constructor
  · intro h i hij hib
    exact h ⟨i, by omega⟩ hij
  · intro h i hij
    exact h i.val hij (by omega)

/-- The finite, Option-equality authentication implies the former
existential-generation definition at the SAME bounded position. -/
theorem resetOutwardDigitOld {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1))
    (h : ResetOutwardDigit ring G root j) :
    ResetNewestOutward ring G root j.val := by
  obtain ⟨_, hsome, hmatch, htok⟩ := h
  cases hlast : G.lastLaunch root with
  | none =>
      simp [hlast] at hsome
  | some gen =>
      refine ⟨gen, hlast, ?_, htok⟩
      simpa only [hlast] using hmatch

theorem resetLeftwardDigitOld {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q) (root : Fin n)
    (j : Fin ((compileAdvice q).b + 1))
    (h : ResetLeftwardDigit ring G root j) :
    ResetNewestLeftward ring G root j.val := by
  obtain ⟨_, hsome, hmatch, htok⟩ := h
  cases hlast : G.lastLaunch root with
  | none =>
      simp [hlast] at hsome
  | some gen =>
      refine ⟨gen, hlast, ?_, htok⟩
      simpa only [hlast] using hmatch

/-- No arbitrary initial private RR/RL gains a generation at cut. -/
theorem resetBoundedInitial {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (cut : Nat) :
    ResetNewestSweepBounded ring root (resetGhostInit C cut) := by
  constructor
  · intro j h
    have hs := h.2.1
    change false = true at hs
    cases hs
  · intro j h
    have hs := h.2.1
    change false = true at hs
    cases hs

/-! Finite, computational mirrors. The proofs below use no
Decidable instance for a quantified Prop. All computation occurs in
Bool-valued list folds; List.all_eq_true reflects the result back
into ordinary Lean propositions. -/

/-- Checks every physical digit index and every potential swept
prefix/suffix index, rather than asking 'decide' to elaborate a
noncomputable Decidable instance for ResetNewestSweepBounded. -/
def resetSweepCheckB {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) : Bool :=
  let indices := List.range ((compileAdvice q).b + 1)
  indices.all (fun j =>
    (indices.all (fun i =>
      decide (
        (0 < j ∧
          (G.lastLaunch root).isSome = true ∧
          G.marks (site ring root j) = G.lastLaunch root ∧
          (G.physical (site ring root j)).tok = .RR) →
        (0 < i → i < j →
          (G.physical (site ring root i)).bit = false ∧
          (G.physical (site ring root i)).tok = .E)))) &&
    (indices.all (fun i =>
      decide (
        (0 < j ∧
          (G.lastLaunch root).isSome = true ∧
          G.marks (site ring root j) = G.lastLaunch root ∧
          (G.physical (site ring root j)).tok = .RL) →
        (j < i →
          (G.physical (site ring root i)).bit = false ∧
          (G.physical (site ring root i)).tok = .E)))))

/-- Soundness is structural, valid for every q, n and ring. -/
theorem resetSweepCheckB_sound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (h : resetSweepCheckB ring root G = true) :
    ResetNewestSweepBounded ring root G := by
  unfold resetSweepCheckB at h
  constructor
  · intro j hfront i hi hij
    have hrow := List.all_eq_true.mp h j.val
      (List.mem_range.mpr j.isLt)
    have hp := (Bool.and_eq_true_iff.mp hrow).1
    have hslot := List.all_eq_true.mp hp i.val
      (List.mem_range.mpr i.isLt)
    have hlogical := of_decide_eq_true hslot
    exact hlogical hfront hi hij
  · intro j hfront i hij
    have hrow := List.all_eq_true.mp h j.val
      (List.mem_range.mpr j.isLt)
    have hp := (Bool.and_eq_true_iff.mp hrow).2
    have hslot := List.all_eq_true.mp hp i.val
      (List.mem_range.mpr i.isLt)
    have hlogical := of_decide_eq_true hslot
    exact hlogical hfront hij

/-- Finite Boolean mirror of Complete, including the root. -/
def resetCompleteCheckB {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : Bool :=
  (List.range ((compileAdvice q).b + 1)).all
    (fun j => decide ((C (site ring root j)).pack.val = j))

theorem resetCompleteCheckB_sound {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (h : resetCompleteCheckB ring C root = true) :
    ResetFiniteComplete ring C root := by
  unfold resetCompleteCheckB at h
  intro j
  have hj := List.all_eq_true.mp h j.val
    (List.mem_range.mpr j.isLt)
  exact of_decide_eq_true hj

/-- A real launch at root=0 of the q=80, n=20 example is a sound
bounded front, despite falsifying the old unbounded definition. -/
theorem resetExampleBoundedLaunch :
    ResetNewestSweepBounded resetAliasRing (0 : Fin 20)
      resetExampleAfter := by
  apply resetSweepCheckB_sound
  decide +kernel

theorem resetExampleBoundedFront :
    ResetOutwardDigit resetAliasRing resetExampleAfter (0 : Fin 20)
      (⟨1, by decide⟩ : Fin ((compileAdvice 80).b + 1)) := by
  unfold ResetOutwardDigit
  decide +kernel

/-- The old alias 21 is not a member of the repaired index type. -/
theorem resetExampleAliasOutside :
    ¬ (21 < (compileAdvice 80).b + 1) := by
  decide +kernel

/-! Actual, ordered BANK row partition. Both classifiers are
executable labels for OLD guards. They do not replace bankPair,
and equality of every symbolic residual outcome is not asserted. -/

inductive ResetGuardWinner where
  | launch | forward | turn | retreat | residual
  deriving DecidableEq, Repr

def resetGuardWinner {c : Compiled}
    (x y : Agent c) : ResetGuardWinner :=
  if resetLaunchGuard x y then .launch
  else if resetForwardGuard x y then .forward
  else if resetTurnGuard x y then .turn
  else if resetRetreatGuard x y then .retreat
  else .residual

/-- Exhaustive Boolean partition: the residual case has all four
literal reset owner guards false, not unchanged BANK fields. -/
theorem resetGuardResidualIff {c : Compiled} (x y : Agent c) :
    resetGuardWinner x y = .residual ↔
      resetLaunchGuard x y = false ∧
      resetForwardGuard x y = false ∧
      resetTurnGuard x y = false ∧
      resetRetreatGuard x y = false := by
  cases hl : resetLaunchGuard x y <;>
    cases hf : resetForwardGuard x y <;>
    cases ht : resetTurnGuard x y <;>
    cases hr : resetRetreatGuard x y <;>
    simp [resetGuardWinner, hl, hf, ht, hr]

/-- Root-side residual rows. The actual owner checks grant and
PACK normalization first, then RESET, returns, ARMED and CSTART.
The width-one fallback is irrelevant in q=80 (b=18). -/
inductive ResetRootRow where
  | notRoot | grantExit | changedRole | wrongNeighbor
  | launch | resetReturn | incrementReturn | comparisonReturn
  | otherReturn | armedCollision | armedSet | armedIssue
  | compareCollision | compareIssue | widthOne | waiting
  deriving DecidableEq, Repr

def resetRootRow (x y : BankCell) (postRole b : Nat) :
    ResetRootRow :=
  if x.role != 0 then .notRoot
  else if x.grant then .grantExit
  else if postRole != y.role then .changedRole
  else if postRole != 1 then .wrongNeighbor
  else if x.mode == .RESET then .launch
  else if isRetTok y.tok then
    if y.tok == .RL && x.mode == .RWAIT then .resetReturn
    else if y.tok == .AL && x.mode == .IWAIT then .incrementReturn
    else if (y.tok == .CL0 || y.tok == .CL1) &&
        x.mode == .CWAIT then .comparisonReturn
    else .otherReturn
  else if x.mode == .ARMED then
    if y.tok != .E then .armedCollision
    else if y.bit == false then .armedSet
    else .armedIssue
  else if x.mode == .CSTART then
    if y.tok != .E then .compareCollision
    else .compareIssue
  else if b == 1 then .widthOne
  else .waiting

/-- Interior rows are in the literal first-match order. At the
rightmost digit an inherited IR is erased BEFORE these guards. -/
inductive ResetInteriorRow where
  | roleChanged | otherGeometry
  | forward | turn | retreat
  | collision | comparisonTurn | otherReturn
  | incrementToggle | comparisonAdvance | frame
  deriving DecidableEq, Repr

def resetInteriorRow (x y : BankCell)
    (postRole b : Nat) : ResetInteriorRow :=
  if postRole != y.role then .roleChanged
  else if !(1 ≤ x.role && x.role < b && y.role == x.role + 1) then
    .otherGeometry
  else
    let yTok := if y.role == b && y.tok == .IR then BTok.E
      else y.tok
    if x.tok == .RR then .forward
    else if y.role == b && yTok == .RR then .turn
    else if yTok == .RL then .retreat
    else if x.tok != .E && yTok != .E then .collision
    else if y.role == b && (yTok == .CR0 || yTok == .CR1) then
      .comparisonTurn
    else if yTok == .AL || yTok == .CL0 || yTok == .CL1 then
      .otherReturn
    else if x.tok == .IR then .incrementToggle
    else if x.tok == .CR0 || x.tok == .CR1 then
      .comparisonAdvance
    else .frame

/-- Actual OLD BANK pair used by Base.baseStep in spatial mode. -/
def resetBankOld {c : Compiled} (x y : Agent c) :
    BankCell × BankCell :=
  bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
    (packNext x.pack.val y.pack.val c.b) c.b c.theta

def resetAgentBankTrip {c : Compiled} (a : Agent c) :
    Mode × Bool × BTok := (a.mode, a.bit, a.tok)

def resetCellBankTrip (a : BankCell) :
    Mode × Bool × BTok := (a.mode, a.bit, a.tok)

/-- Three BANK coordinates come from the actual Base owner,
independent of the certificate event or the token/DCC owners. -/
theorem resetBaseBankTrip {c : Compiled} (ev : CertEvent)
    (x y : Agent c) (hsp : c.useSmall = false) :
    resetAgentBankTrip (baseStep c ev x y).1 =
        resetCellBankTrip (resetBankOld x y).1 ∧
    resetAgentBankTrip (baseStep c ev x y).2 =
        resetCellBankTrip (resetBankOld x y).2 := by
  constructor
  · simp [resetAgentBankTrip, resetCellBankTrip,
      resetBankOld, baseStep, hsp, copyBank,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | exact ⟨rfl, rfl, rfl⟩ | rfl | split)
  · simp [resetAgentBankTrip, resetCellBankTrip,
      resetBankOld, baseStep, hsp, copyBank,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | exact ⟨rfl, rfl, rfl⟩ | rfl | split)

/-- Full Protocol.transition retains precisely the Base BANK slots:
the certificate and H/K assembly do not overwrite them. -/
theorem resetTransitionBankTrip (c : Compiled)
    (x y : Agent c) (hsp : c.useSmall = false) :
    resetAgentBankTrip (transition c x y).1 =
        resetCellBankTrip (resetBankOld x y).1 ∧
    resetAgentBankTrip (transition c x y).2 =
        resetCellBankTrip (resetBankOld x y).2 := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := resetBaseBankTrip ev x y hsp
  simpa [transition, hc, hh, resetAgentBankTrip,
    assemble] using hb

/-- The real protocol's selected two endpoint slots, rather than
a BANK-only hypothetical transition. Source and target are distinct. -/
theorem resetPhysicalEdgeBankTrip {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hsp : (compileAdvice q).useSmall = false) :
    resetAgentBankTrip (((protocol q).step ring C e) e) =
        resetCellBankTrip (resetBankOld
          (C e) (C (ring.rightNeighbor e))).1 ∧
    resetAgentBankTrip
        (((protocol q).step ring C e) (ring.rightNeighbor e)) =
        resetCellBankTrip (resetBankOld
          (C e) (C (ring.rightNeighbor e))).2 := by
  have hb := resetTransitionBankTrip (compileAdvice q)
    (C e) (C (ring.rightNeighbor e)) hsp
  simpa [PopulationProtocol.step, protocol, hne] using hb

/-- An uncolored, unlaunched pair cannot mint a new authenticated
generation. This is the exact residual ghost-row property, not a
claim that the physical BANK slots do not change. -/
theorem resetNoLaunchCannotMintFromEmpty {c : Compiled}
    (x y nx ny : Agent c) (stamp : Nat)
    (hn : resetLaunchGuard x y = false) :
    resetTagPair x y nx ny none none stamp = (none, none) := by
  simp [resetTagPair, resetScreen, hn]

/-- No IR source can be hidden strictly inside a swept prefix. -/
theorem resetPrefixPrecludesIR {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (front i : Nat)
    (hp : PrefixClear ring C root front)
    (hi : 1 ≤ i) (hif : i < front) :
    (C (site ring root i)).tok ≠ .IR := by
  intro hir
  have hclear := (hp i hi hif).2
  rw [hir] at hclear
  cases hclear

/-- Likewise for an IR source in the cleared return suffix. -/
theorem resetSuffixPrecludesIR {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (front i : Nat)
    (hs : SuffixClear ring C root front)
    (hif : front < i) (hib : i ≤ (compileAdvice q).b) :
    (C (site ring root i)).tok ≠ .IR := by
  intro hir
  have hclear := (hs i hif hib).2
  rw [hir] at hclear
  cases hclear

/-! Kernel finite probes of the selected non-reset rows. These
are examples of literal bankPair, not general symbolic case lemmas. -/

private def resetProbeArmedRoot : BankCell :=
  { rowCell 0 false .E with mode := .ARMED }

private def resetProbeCompareRoot : BankCell :=
  { rowCell 0 false .E with mode := .CSTART }

private def resetProbeWaitingRoot : BankCell :=
  { rowCell 0 false .E with mode := .RWAIT, lease := 1 }

theorem resetProbeArmedSetsOne :
    let z := bankPair resetProbeArmedRoot
      (rowCell 1 false .E) 1 18 (fun _ => false)
    resetRootRow resetProbeArmedRoot (rowCell 1 false .E)
       1 18 = .armedSet ∧
      z.1.mode = .CSTART ∧ z.2.bit = true ∧
      z.2.tok = .E := by
  decide +kernel

theorem resetProbeArmedIssuesIncrement :
    let z := bankPair resetProbeArmedRoot
      (rowCell 1 true .E) 1 18 (fun _ => false)
    resetRootRow resetProbeArmedRoot (rowCell 1 true .E)
       1 18 = .armedIssue ∧
      z.1.mode = .IWAIT ∧ z.2.bit = false ∧
      z.2.tok = .IR := by
  decide +kernel

theorem resetProbeComparisonIssue :
    let z := bankPair resetProbeCompareRoot
      (rowCell 1 false .E) 1 18 (fun _ => false)
    resetRootRow resetProbeCompareRoot (rowCell 1 false .E)
       1 18 = .compareIssue ∧
      z.1.mode = .CWAIT ∧ z.2.bit = false ∧
      z.2.tok = .CR1 := by
  decide +kernel

theorem resetProbeReturnToArmed :
    let z := bankPair resetProbeWaitingRoot
      (rowCell 1 false .RL) 1 18 (fun _ => false)
    resetRootRow resetProbeWaitingRoot (rowCell 1 false .RL)
       1 18 = .resetReturn ∧
      z.1.mode = .ARMED ∧ z.2.bit = false ∧
      z.2.tok = .E := by
  decide +kernel

theorem resetProbeWaitingTimeout :
    let z := bankPair resetProbeWaitingRoot
      (rowCell 1 false .E) 1 18 (fun _ => false)
    resetRootRow resetProbeWaitingRoot (rowCell 1 false .E)
       1 18 = .waiting ∧
      z.1.mode = .RESET ∧ z.2.bit = false ∧
      z.2.tok = .E := by
  decide +kernel

theorem resetProbeInteriorCollision :
    let z := bankPair (rowCell 4 false .IR)
      (rowCell 5 true .CR0) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 false .IR) (rowCell 5 true .CR0)
       5 18 = .collision ∧
      z.1.tok = .E ∧ z.2.tok = .E ∧
      z.1.bit = false ∧ z.2.bit = true := by
  decide +kernel

theorem resetProbeInteriorIncrementSetsOne :
    let z := bankPair (rowCell 4 false .IR)
      (rowCell 5 false .E) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 false .IR) (rowCell 5 false .E)
       5 18 = .incrementToggle ∧
      z.1.tok = .E ∧ z.2.bit = true ∧ z.2.tok = .AL := by
  decide +kernel

theorem resetProbeInteriorIncrementClears :
    let z := bankPair (rowCell 4 false .IR)
      (rowCell 5 true .E) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 false .IR) (rowCell 5 true .E)
       5 18 = .incrementToggle ∧
      z.1.tok = .E ∧ z.2.bit = false ∧ z.2.tok = .IR := by
  decide +kernel

theorem resetProbeInteriorComparisonForward :
    let z := bankPair (rowCell 4 false .CR1)
      (rowCell 5 true .E) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 false .CR1) (rowCell 5 true .E)
       5 18 = .comparisonAdvance ∧
      z.1.tok = .E ∧ z.2.bit = true ∧ z.2.tok = .CR0 := by
  decide +kernel

theorem resetProbeInteriorComparisonTurn :
    let z := bankPair (rowCell 17 false .E)
      (rowCell 18 false .CR1) 18 18 (fun _ => false)
    resetInteriorRow (rowCell 17 false .E) (rowCell 18 false .CR1)
       18 18 = .comparisonTurn ∧
      z.1.tok = .CL1 ∧ z.2.tok = .E ∧
      z.1.bit = false ∧ z.2.bit = false := by
  decide +kernel

theorem resetProbeInteriorReturnOther :
    let z := bankPair (rowCell 4 false .E)
      (rowCell 5 true .AL) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 false .E) (rowCell 5 true .AL)
       5 18 = .otherReturn ∧
      z.1.tok = .AL ∧ z.2.tok = .E ∧
      z.1.bit = false ∧ z.2.bit = true := by
  decide +kernel

theorem resetProbeInteriorFrame :
    let z := bankPair (rowCell 4 true .E)
      (rowCell 5 false .E) 5 18 (fun _ => false)
    resetInteriorRow (rowCell 4 true .E) (rowCell 5 false .E)
       5 18 = .frame ∧
      z.1.bit = true ∧ z.2.bit = false ∧
      z.1.tok = .E ∧ z.2.tok = .E := by
  decide +kernel

/-- The four reset rows at real Protocol.transition endpoints.
The selected full owner (not merely a BANK-only simulator) is used. -/
private def resetProbeAgent
    (role : Fin ((compileAdvice 80).b + 2))
    (bit : Bool) (tok : BTok) : Agent (compileAdvice 80) :=
  { Agent.blank (compileAdvice 80) with
    pack := role, bit := bit, tok := tok }

theorem resetProbeRealLaunch :
    let x := resetProbeAgent ⟨0, by decide⟩ false .E
    let y := resetProbeAgent ⟨1, by decide⟩ true .IR
    resetLaunchGuard x y = true ∧
      (transition (compileAdvice 80) x y).1.mode = .RWAIT ∧
      (transition (compileAdvice 80) x y).2.bit = false ∧
      (transition (compileAdvice 80) x y).2.tok = .RR := by
  decide +kernel

theorem resetProbeRealForward :
    let x := resetProbeAgent ⟨4, by decide⟩ false .RR
    let y := resetProbeAgent ⟨5, by decide⟩ true .CL1
    resetForwardGuard x y = true ∧
      (transition (compileAdvice 80) x y).1.tok = .E ∧
      (transition (compileAdvice 80) x y).2.bit = false ∧
      (transition (compileAdvice 80) x y).2.tok = .RR := by
  decide +kernel

theorem resetProbeRealTurn :
    let x := resetProbeAgent ⟨17, by decide⟩ true .E
    let y := resetProbeAgent ⟨18, by decide⟩ false .RR
    resetTurnGuard x y = true ∧
      (transition (compileAdvice 80) x y).1.bit = false ∧
      (transition (compileAdvice 80) x y).1.tok = .RL ∧
      (transition (compileAdvice 80) x y).2.tok = .E := by
  decide +kernel

theorem resetProbeRealRetreat :
    let x := resetProbeAgent ⟨9, by decide⟩ true .IR
    let y := resetProbeAgent ⟨10, by decide⟩ false .RL
    resetRetreatGuard x y = true ∧
      (transition (compileAdvice 80) x y).1.bit = false ∧
      (transition (compileAdvice 80) x y).1.tok = .RL ∧
      (transition (compileAdvice 80) x y).2.tok = .E := by
  decide +kernel

/-! Adversarial check: the bounded snapshot ALONE is not closed on
all artificially populated ResetGhost records. This state starts
with a real advanced front, then changes the root mode by hand.
It is NOT the image of resetGhostWord from the genuine launch. -/

private def resetExampleAfterForward : ResetGhost 20 80 :=
  resetGhostStep resetAliasRing resetExampleAfter (1 : Fin 20)

private def resetForgedArmed : ResetGhost 20 80 :=
  { resetExampleAfterForward with
    physical := fun i =>
      if i = (0 : Fin 20) then
        { (resetExampleAfterForward.physical i) with mode := .ARMED }
      else resetExampleAfterForward.physical i }

/-- Complete, grant-free, role-stable, already-swept finite snapshot:
the no-reset ARMED row writes digit 1 behind the digit-2 newest RR.
This refutes closure from those SNAPSHOT premises alone, not the
paper's historical fresh-launch assertion. -/
theorem resetForgedArmedBreaksBoundedSnapshot :
    Complete resetAliasRing resetForgedArmed.physical (0 : Fin 20) ∧
    GrantFree resetForgedArmed.physical (0 : Fin 20) ∧
    RoleStableEdge resetAliasRing (0 : Fin 20)
      resetForgedArmed.physical (0 : Fin 20) ∧
    ResetNewestSweepBounded resetAliasRing (0 : Fin 20)
      resetForgedArmed ∧
    resetGuardWinner (resetForgedArmed.physical (0 : Fin 20))
      (resetForgedArmed.physical (1 : Fin 20)) = .residual ∧
    ((resetGhostStep resetAliasRing resetForgedArmed
      (0 : Fin 20)).physical (1 : Fin 20)).bit = true ∧
    ¬ ResetNewestSweepBounded resetAliasRing (0 : Fin 20)
      (resetGhostStep resetAliasRing resetForgedArmed
        (0 : Fin 20)) := by
  have hc : Complete resetAliasRing resetForgedArmed.physical
      (0 : Fin 20) := by
    apply (resetCompleteIffFinite _ _ _).2
    apply resetCompleteCheckB_sound
    decide +kernel
  have hr : RoleStableEdge resetAliasRing (0 : Fin 20)
      resetForgedArmed.physical (0 : Fin 20) := by
    have hh := internal_roles_fixed resetAliasRing
      resetForgedArmed.physical (0 : Fin 20) 0 hc
      (by decide +kernel : 0 < (compileAdvice 80).b)
    intro j _
    exact congrFun hh (site resetAliasRing (0 : Fin 20) j)
  refine ⟨hc, ?_, hr, ?_, ?_, ?_, ?_⟩
  · change (resetForgedArmed.physical (0 : Fin 20)).grant = false
    decide +kernel
  · apply resetSweepCheckB_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · intro hs
    have hfront : ResetOutwardDigit resetAliasRing
        (resetGhostStep resetAliasRing resetForgedArmed (0 : Fin 20))
        (0 : Fin 20)
        (⟨2, by decide⟩ : Fin ((compileAdvice 80).b + 1)) := by
      unfold ResetOutwardDigit
      decide +kernel
    have hdirty :
        ((resetGhostStep resetAliasRing resetForgedArmed
          (0 : Fin 20)).physical
          (site resetAliasRing (0 : Fin 20) 1)).bit = true := by
      decide +kernel
    have hclear := (hs.1 _ hfront)
      (⟨1, by decide⟩ : Fin ((compileAdvice 80).b + 1))
      (by decide) (by decide)
    have hfalse := hclear.1
    rw [hdirty] at hfalse
    cases hfalse

/-- A named additional causal invariant needed to rule out the
forged ARMED-root state while a newest reset worker is in flight.
It is only defined here, not postulated as holding on every ghost. -/
def ResetActiveRootDiscipline {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (G : ResetGhost n q) : Prop :=
  (∃ j : Fin ((compileAdvice q).b + 1),
    ResetOutwardDigit ring G root j ∨
    ResetLeftwardDigit ring G root j) →
  (G.physical root).mode ≠ .ARMED ∧
    (G.physical root).mode ≠ .CSTART

/-- Distinct complete roles imply distinct PHYSICAL interval sites. -/
theorem resetCompleteSitesDifferent {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n)
    (hc : Complete ring C root)
    (i j : Nat) (hi : i ≤ (compileAdvice q).b)
    (hj : j ≤ (compileAdvice q).b) (hij : i ≠ j) :
    site ring root i ≠ site ring root j := by
  intro heq
  have ha := hc i hi
  have hb := hc j hj
  rw [heq] at ha
  omega

/-- Conditional endpoint assembly for the paper's part (c).
If the genuine final root service consumes RL and leaves digit 1
zero, and the actual authenticated RL at digit 1 has its entire
suffix cleared, every active digit is zero and worker-empty afterward.
The historical establishment of the hypotheses is still missing. -/
theorem resetFinalReturnOfClearedSuffix {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n)
    (hc : Complete ring C root)
    (hs : SuffixClear ring C root 1)
    (hconsumed :
      (((protocol q).step ring C root) (site ring root 1)).bit =
          false ∧
      (((protocol q).step ring C root) (site ring root 1)).tok =
          .E) :
    ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root) (site ring root j)).bit =
          false ∧
      (((protocol q).step ring C root) (site ring root j)).tok =
          .E := by
  intro j hj hb
  by_cases hone : j = 1
  · simpa only [hone] using hconsumed
  · have hzero : j ≠ 0 := by omega
    have hleft :=
      resetCompleteSitesDifferent ring C root hc j 0 hb
        (by omega) hzero
    have hright :=
      resetCompleteSitesDifferent ring C root hc j 1 hb
        (by omega) hone
    change site ring root j ≠ root at hleft
    change site ring root j ≠ ring.rightNeighbor root at hright
    have hframe := step_frame ring C root (site ring root j)
      hleft hright
    rw [hframe]
    exact hs j (by omega) hb

/-! ## Symbolic non-reset outputs and no-promotion facts

All new claims in this section are about the same old→new pair
functions as the machine, not a strengthened ghost transition. -/

/-- Literal root ARMED row, first non-reset bit writer. Under the
declared unchanged roles, empty responder token and zero bit, the
BANK pair sets the bit to one and enters CSTART. -/
theorem resetBankArmedSetSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false)
    (hb : 1 ≤ b) :
    let z := bankPair x y 1 b theta
    z.1.mode = .CSTART ∧ z.2.bit = true ∧
      z.2.tok = .E := by
  simp [bankPair, hr, hg, hy, hm, ht, hbit, hb,
    isRetTok]

/-- ARMED with bit one is a different active row: it issues IR,
clears that bit and waits for the increment return. -/
theorem resetBankArmedIssueSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true)
    (hb : 1 ≤ b) :
    let z := bankPair x y 1 b theta
    z.1.mode = .IWAIT ∧ z.2.bit = false ∧
      z.2.tok = .IR := by
  simp [bankPair, hr, hg, hy, hm, ht, hbit, hb,
    isRetTok]

/-- Symbolic internal non-reset bit writer. With empty destination
worker and incoming IR, its exact write is a toggle: on zero it
produces a leftward AL, on one a continuing IR. -/
theorem resetBankIncrementToggleSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E) :
    let z := bankPair x y y.role b theta
    z.1.tok = .E ∧ z.2.bit = !y.bit ∧
      z.2.tok = (if y.bit then .IR else .AL) := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  simp [bankPair, hxne, hyne, hx, hlt, hxle,
    hy, hyle, hypos, hxb, htx, hty]

/-- If the launch guard is false, a fresh stamp cannot arise from
a pair of old labels that both differ from that stamp. This
includes arbitrary old worker bytes and arbitrary distinct older
generations. It is stronger than the none/none special case. -/
theorem resetTagPairNoStampPromotion {c : Compiled}
    (x y nx ny : Agent c) (tagX tagY : ResetGeneration)
    (stamp gen : Nat)
    (hlaunch : resetLaunchGuard x y = false)
    (hx : tagX ≠ some gen) (hy : tagY ≠ some gen) :
    (resetTagPair x y nx ny tagX tagY stamp).1 ≠ some gen ∧
    (resetTagPair x y nx ny tagX tagY stamp).2 ≠ some gen := by
  constructor
  · intro h
    unfold resetTagPair resetScreen at h
    simp only [hlaunch, Bool.false_eq_true, ite_false] at h
    (repeat' split at h) <;> simp [hx, hy] at h
  · intro h
    unfold resetTagPair resetScreen at h
    simp only [hlaunch, Bool.false_eq_true, ite_false] at h
    (repeat' split at h) <;> simp [hx, hy] at h

/-- Causal root discipline is true on arbitrary initial Cartesian
scratch because all generations are untrusted at resetGhostInit.
Word preservation still needs a nontrivial step proof. -/
theorem resetActiveRootDisciplineInit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (cut : Nat) :
    ResetActiveRootDiscipline ring root (resetGhostInit C cut) := by
  intro h
  obtain ⟨j, hfront⟩ := h
  cases hfront with
  | inl hout =>
      have hh := hout.2.1
      change false = true at hh
      cases hh
  | inr hback =>
      have hh := hback.2.1
      change false = true at hh
      cases hh


end Counter
end L3


/-! ## Causal reset-worker prerequisites

A stamped wait is tracked independently of arbitrary Cartesian
scratch. No-launch nonpromotion is proved for every physical ghost
step and word. A returning-prefix barrier is necessary in addition
to the bounded suffix sweep: an exact forged witness below refutes
closure of those weaker predicates, not genuine reset trajectories.
The full causal front and lease preservation remain open.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-! ### Stamped wait and the root mode. -/

/-- A stamped waiting root necessarily has physical role zero and
mode RWAIT. The stamp is screened by the old/new selected pair. -/
def ResetStampedWaitMode {n q : Nat} (G : ResetGhost n q) : Prop :=
  ∀ i gen, G.waits i = some gen →
    (G.physical i).pack.val = 0 ∧
      (G.physical i).mode = .RWAIT

theorem resetStampedWaitModeInit {n q : Nat}
    (C : Config q n) (cut : Nat) :
    ResetStampedWaitMode (resetGhostInit C cut) := by
  intro i gen h
  cases h

/-- Exact values of the ghost wait register on the original
selected edge. No new physical transition is introduced. -/
theorem resetGhostWaitsEq {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (e i : Fin n) :
    (resetGhostStep ring G e).waits i =
      if i = e then
        (resetWaitPair (G.physical e)
          (G.physical (ring.rightNeighbor e))
          ((protocol q).step ring G.physical e e)
          ((protocol q).step ring G.physical e
            (ring.rightNeighbor e))
          (G.waits e) (G.waits (ring.rightNeighbor e))
          (G.clock + 1)).1
      else if i = ring.rightNeighbor e then
        (resetWaitPair (G.physical e)
          (G.physical (ring.rightNeighbor e))
          ((protocol q).step ring G.physical e e)
          ((protocol q).step ring G.physical e
            (ring.rightNeighbor e))
          (G.waits e) (G.waits (ring.rightNeighbor e))
          (G.clock + 1)).2
      else G.waits i := rfl

/-- Mode custody is preserved through ALL actual BANK rows,
including the active non-reset complement. -/
theorem resetStampedWaitModeStep {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (e : Fin n) (h : ResetStampedWaitMode G) :
    ResetStampedWaitMode (resetGhostStep ring G e) := by
  intro i gen htag
  rw [resetGhostWaitsEq] at htag
  by_cases hi : i = e
  · subst i
    rw [if_pos rfl] at htag
    exact reset_wait_source_sound _ _ _ _ _ _ _ _ htag
  · rw [if_neg hi] at htag
    by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [if_pos rfl] at htag
      exact reset_wait_target_sound _ _ _ _ _ _ _ _ htag
    · rw [if_neg hj] at htag
      have hold := h i gen htag
      have hframe : (protocol q).step ring G.physical e i =
          G.physical i :=
        step_frame ring G.physical e i hi hj
      rw [resetGhost_projection, hframe]
      exact hold

theorem resetStampedWaitModeWord {n q : Nat}
    (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (G : ResetGhost n q),
      ResetStampedWaitMode G →
      ResetStampedWaitMode (resetGhostWord ring w G) := by
  intro w
  induction w with
  | nil =>
      intro G h
      exact h
  | cons e es ih =>
      intro G h
      exact ih (resetGhostStep ring G e)
        (resetStampedWaitModeStep ring G e h)

/-- The requested stronger causal lease invariant, including
matching root generation and a positive physical lease. Unlike
the previous mode-only lemma, the step closure of this Prop is
not claimed. -/
def ResetRootLeaseCoherence {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) : Prop :=
  ResetStampedWaitMode G ∧
  (∀ gen, G.waits root = some gen →
    0 < (G.physical root).lease.val ∧
      G.lastLaunch root = some gen) ∧
  ((∃ j : Fin ((compileAdvice q).b + 1),
      ResetOutwardDigit ring G root j ∨
        ResetLeftwardDigit ring G root j) →
    (G.physical root).mode = .RWAIT ∨
      (G.physical root).mode = .RESET)

theorem resetRootLeaseCoherenceInit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (cut : Nat) :
    ResetRootLeaseCoherence ring root (resetGhostInit C cut) := by
  refine ⟨resetStampedWaitModeInit C cut, ?_, ?_⟩
  · intro gen h
    cases h
  · intro h
    obtain ⟨j, hj⟩ := h
    rcases hj with ho | hl
    · have hn := ho.2.1
      change false = true at hn
      cases hn
    · have hn := hl.2.1
      change false = true at hn
      cases hn

theorem resetRootLeaseCoherenceDiscipline {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (h : ResetRootLeaseCoherence ring root G) :
    ResetActiveRootDiscipline ring root G := by
  intro hf
  have hm := h.2.2 hf
  constructor
  · intro bad
    rcases hm with hr | hr
    · rw [hr] at bad
      cases bad
    · rw [hr] at bad
      cases bad
  · intro bad
    rcases hm with hr | hr
    · rw [hr] at bad
      cases bad
    · rw [hr] at bad
      cases bad

/-! ### Nonpromotion of a generation on actual no-launch edges. -/

theorem resetNoGenerationMintStep {n q : Nat}
    (ring : DirectedRing n) (G : ResetGhost n q)
    (e : Fin n) (gen : Nat)
    (hno : resetLaunchGuard (G.physical e)
      (G.physical (ring.rightNeighbor e)) = false)
    (hgone : ∀ i, G.marks i ≠ some gen) :
    ∀ i, (resetGhostStep ring G e).marks i ≠ some gen := by
  have hp := resetTagPairNoStampPromotion
    (G.physical e) (G.physical (ring.rightNeighbor e))
    ((protocol q).step ring G.physical e e)
    ((protocol q).step ring G.physical e
      (ring.rightNeighbor e))
    (G.marks e) (G.marks (ring.rightNeighbor e))
    (G.clock + 1) gen hno
    (hgone e) (hgone (ring.rightNeighbor e))
  intro i
  rw [resetGhost_marks_eq]
  by_cases hi : i = e
  · rw [if_pos hi]
    exact hp.1
  · rw [if_neg hi]
    by_cases hj : i = ring.rightNeighbor e
    · rw [if_pos hj]
      exact hp.2
    · rw [if_neg hj]
      exact hgone i

/-- A no-launch WORD tests each selected edge at its own
intermediate physical configuration, not only the initial cut. -/
def ResetNoLaunchWord {n q : Nat}
    (ring : DirectedRing n) :
    ResetGhost n q → List (Fin n) → Prop
  | _, [] => True
  | G, e :: es =>
      resetLaunchGuard (G.physical e)
        (G.physical (ring.rightNeighbor e)) = false ∧
      ResetNoLaunchWord ring (resetGhostStep ring G e) es

theorem resetNoGenerationMintWord {n q : Nat}
    (ring : DirectedRing n) (gen : Nat) :
    ∀ (w : List (Fin n)) (G : ResetGhost n q),
      ResetNoLaunchWord ring G w →
      (∀ i, G.marks i ≠ some gen) →
      ∀ i, (resetGhostWord ring w G).marks i ≠ some gen := by
  intro w
  induction w with
  | nil =>
      intro G hw hgone
      exact hgone
  | cons e es ih =>
      intro G hw hgone
      exact ih (resetGhostStep ring G e) hw.2
        (resetNoGenerationMintStep ring G e gen hw.1 hgone)

/-! ### Additional returning-prefix barrier. -/

/-- The original bounded leftward predicate clears only a
suffix. A returning newest-generation RL also needs a cleared
prefix to rule out an unrelated earlier return at digit one. -/
def ResetReturnPrefixClear {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q) : Prop :=
  ∀ j : Fin ((compileAdvice q).b + 1),
    ResetLeftwardDigit ring G root j →
      ResetPrefixDigit ring G.physical root j

theorem resetReturnPrefixClearInit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (cut : Nat) :
    ResetReturnPrefixClear ring root (resetGhostInit C cut) := by
  intro j h
  have hn := h.2.1
  change false = true at hn
  cases hn

theorem resetReturnPrefixExcludesOlderAtOne {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (hbar : ResetReturnPrefixClear ring root G)
    (j : Fin ((compileAdvice q).b + 1))
    (hfront : ResetLeftwardDigit ring G root j)
    (hj : 1 < j.val) :
    (G.physical (site ring root 1)).bit = false ∧
      (G.physical (site ring root 1)).tok = .E := by
  have hbound : 1 < (compileAdvice q).b + 1 :=
    Nat.lt_trans hj j.isLt
  exact hbar j hfront ⟨1, hbound⟩
    (by show 0 < (1 : Nat); omega) hj


/-! ### Forged returning ghost, distinguishing the history gap. -/

private def resetForgedDoubleReturn : ResetGhost 20 80 :=
  { resetExampleAfterForward with
    physical := fun z =>
      if z = (1 : Fin 20) then
        { (resetExampleAfterForward.physical z) with tok := .RL }
      else if z = (2 : Fin 20) then
        { (resetExampleAfterForward.physical z) with tok := .RL }
      else resetExampleAfterForward.physical z }

/-- The literal root RWAIT/old-RL first-match BANK return enters
ARMED while the separately stamped RL at digit two survives.
Before this step Complete, GrantFree, role stability, bounded
sweep and the old root discipline ALL hold. This is a forged
ghost, not a trace from resetGhostInit. -/
theorem resetForgedReturnBreaksDiscipline :
    ∃ G : ResetGhost 20 80,
      Complete resetAliasRing G.physical (0 : Fin 20) ∧
      GrantFree G.physical (0 : Fin 20) ∧
      RoleStableEdge resetAliasRing (0 : Fin 20)
        G.physical (0 : Fin 20) ∧
      ResetNewestSweepBounded resetAliasRing (0 : Fin 20) G ∧
      ResetActiveRootDiscipline resetAliasRing (0 : Fin 20) G ∧
      ¬ ResetActiveRootDiscipline resetAliasRing (0 : Fin 20)
        (resetGhostStep resetAliasRing G (0 : Fin 20)) := by
  have hc : Complete resetAliasRing
      resetForgedDoubleReturn.physical (0 : Fin 20) := by
    apply (resetCompleteIffFinite _ _ _).2
    apply resetCompleteCheckB_sound
    decide +kernel
  have hr : RoleStableEdge resetAliasRing (0 : Fin 20)
      resetForgedDoubleReturn.physical (0 : Fin 20) := by
    have hh := internal_roles_fixed resetAliasRing
      resetForgedDoubleReturn.physical (0 : Fin 20) 0 hc
      (by decide +kernel : 0 < (compileAdvice 80).b)
    intro j hj
    exact congrFun hh (site resetAliasRing (0 : Fin 20) j)
  refine ⟨resetForgedDoubleReturn, hc, ?_, hr, ?_, ?_, ?_⟩
  · change (resetForgedDoubleReturn.physical
        (0 : Fin 20)).grant = false
    decide +kernel
  · apply resetSweepCheckB_sound
    decide +kernel
  · intro _
    constructor
    · decide +kernel
    · decide +kernel
  · intro hd
    have hfront : ResetLeftwardDigit resetAliasRing
        (resetGhostStep resetAliasRing resetForgedDoubleReturn
          (0 : Fin 20))
        (0 : Fin 20)
        (⟨2, by decide⟩ : Fin ((compileAdvice 80).b + 1)) := by
      unfold ResetLeftwardDigit
      decide +kernel
    have hmode :
        ((resetGhostStep resetAliasRing resetForgedDoubleReturn
          (0 : Fin 20)).physical (0 : Fin 20)).mode =
          .ARMED := by
      decide +kernel
    exact (hd ⟨⟨2, by decide⟩, Or.inr hfront⟩).1 hmode

/-! ### Literal Base BANK RL return and terminal physical part (c). -/

/-- Actual root RWAIT / RL branch: consume the RL, enter
ARMED and leave the bit unchanged. Here the returned RL bit
is known to be zero from its preceding retreat. -/
theorem resetBankConsumeRl
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RWAIT)
    (ht : y.tok = .RL) (hbit : y.bit = false)
    (hb : 1 ≤ b) :
    let z := bankPair x y 1 b theta
    z.1.mode = .ARMED ∧ z.2.bit = false ∧
      z.2.tok = .E := by
  simp [bankPair, hr, hg, hy, hm, ht, hbit, hb, isRetTok]

/-- For a ring of at least two, the root is not its own
outgoing-edge responder. -/
theorem resetRootPortDistinct {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n) : ring.rightNeighbor root ≠ root := by
  intro he
  have hv := congrArg Fin.val he
  change (root.val + 1) % n = root.val at hv
  by_cases hh : root.val + 1 < n
  · rw [Nat.mod_eq_of_lt hh] at hv
    omega
  · have heq : root.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- Lift the exact root RL row through the full
Protocol.transition to the original physical selected edge. -/
theorem resetPhysicalRootConsumeRl {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (hb : 1 ≤ (compileAdvice q).b)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hm : (C root).mode = .RWAIT)
    (ht : (C (site ring root 1)).tok = .RL)
    (hbit : (C (site ring root 1)).bit = false) :
    (((protocol q).step ring C root)
      (site ring root 1)).bit = false ∧
    (((protocol q).step ring C root)
      (site ring root 1)).tok = .E := by
  let y := ring.rightNeighbor root
  have hzero : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C y).pack.val = 1 := by
    simpa only [y, site] using hc 1 (by omega)
  have htok : (C y).tok = .RL := by
    simpa only [y, site] using ht
  have hfirstBit : (C y).bit = false := by
    simpa only [y, site] using hbit
  have hgrant : (C root).grant = false := hg
  have hpositive : 0 < (compileAdvice q).b := by omega
  have hpost :
      packNext (C root).pack.val (C y).pack.val
        (compileAdvice q).b = 1 := by
    rw [hzero, hone]
    simp [packNext, hpositive]
  have hbank :
      ((resetBankOld (C root) (C y)).2).bit = false ∧
      ((resetBankOld (C root) (C y)).2).tok = .E := by
    unfold resetBankOld
    rw [hpost]
    have hr := resetBankConsumeRl
      (bankCell (C root) (C root).pack.val)
      (bankCell (C y) (C y).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by simpa [bankCell] using hzero)
      (by simpa [bankCell] using hgrant)
      (by simpa [bankCell] using hone)
      (by simpa [bankCell] using hm)
      (by simpa [bankCell] using htok)
      (by simpa [bankCell] using hfirstBit) hb
    exact hr.2
  have hprojection :=
    (resetPhysicalEdgeBankTrip ring C root
      (resetRootPortDistinct ring root hn) hsp).2
  have hpair := congrArg
    (fun z : Mode × Bool × BTok => z.2) hprojection
  change
    ((((protocol q).step ring C root) y).bit,
      (((protocol q).step ring C root) y).tok) =
    (((resetBankOld (C root) (C y)).2).bit,
      ((resetBankOld (C root) (C y)).2).tok) at hpair
  rw [hbank.1, hbank.2] at hpair
  change
    (((protocol q).step ring C root) y).bit = false ∧
      (((protocol q).step ring C root) y).tok = .E
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- Appendix C(c), the verified physical terminal step: when
a newest stamped RL at digit 1 has a swept suffix, bit 1 is
zero and the root is grant-free RWAIT, the real service leaves
all b digits zero and worker-empty. Establishing these
hypotheses along every historical reset remains open. -/
theorem resetPartCAtCertifiedReturn {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (hn : 2 ≤ n) (hsp : (compileAdvice q).useSmall = false)
    (hb : 1 ≤ (compileAdvice q).b)
    (hc : Complete ring G.physical root)
    (hg : GrantFree G.physical root)
    (hm : (G.physical root).mode = .RWAIT)
    (hsweep : ResetNewestSweepBounded ring root G)
    (hfront : ResetLeftwardDigit ring G root
      (⟨1, by omega⟩ : Fin ((compileAdvice q).b + 1)))
    (hbit : (G.physical (site ring root 1)).bit = false) :
    ∀ j, 1 ≤ j → j ≤ (compileAdvice q).b →
      (((protocol q).step ring G.physical root)
        (site ring root j)).bit = false ∧
      (((protocol q).step ring G.physical root)
        (site ring root j)).tok = .E := by
  let one : Fin ((compileAdvice q).b + 1) := ⟨1, by omega⟩
  have hright : SuffixClear ring G.physical root 1 :=
    (resetSuffixDigitIffOld ring G.physical root one).1
      (hsweep.2 one hfront)
  have htok : (G.physical (site ring root 1)).tok = .RL :=
    hfront.2.2.2
  have hconsume := resetPhysicalRootConsumeRl
    ring G.physical root hn hsp hb hc hg hm htok hbit
  exact resetFinalReturnOfClearedSuffix
    ring G.physical root hc hright hconsume


/-! ### Exact exclusion of the ordinary IR bit writer within
already-cleared regions, assuming the corresponding authentic
front snapshot at this very cut. The remaining root ARMED row is
handled by a separate root-mode premise. -/

/-- The source of an IR toggle entering a digit k>=2 behind an
outward front would be digit k-1, which is worker-empty. -/
theorem resetOutwardPrefixNoIRSource {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (hsweep : ResetNewestSweepBounded ring root G)
    (j : Fin ((compileAdvice q).b + 1))
    (hfront : ResetOutwardDigit ring G root j)
    (k : Nat) (hk : 2 ≤ k) (hkj : k < j.val) :
    (G.physical (site ring root (k - 1))).tok ≠ .IR := by
  have hp : PrefixClear ring G.physical root j.val :=
    (resetPrefixDigitIffOld ring G.physical root j).1
      (hsweep.1 j hfront)
  exact resetPrefixPrecludesIR ring G.physical root
    j.val (k - 1) hp (by omega) (by omega)

/-- An active newest worker together with the already-defined
root discipline excludes the ARMED branch that writes bit one
at digit one. This is conditional on that discipline, whose
universal role-stable closure remains open. -/
theorem resetNewestRootNoArmed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (hmode : ResetActiveRootDiscipline ring root G)
    (j : Fin ((compileAdvice q).b + 1))
    (hfront : ResetOutwardDigit ring G root j ∨
      ResetLeftwardDigit ring G root j) :
    (G.physical root).mode ≠ .ARMED := by
  exact (hmode ⟨j, hfront⟩).1

/-- An IR source strictly inside the cleared returning suffix
is impossible; the source at the RL front is itself RL, not IR. -/
theorem resetReturningSuffixNoIRSource {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (G : ResetGhost n q)
    (hsweep : ResetNewestSweepBounded ring root G)
    (j : Fin ((compileAdvice q).b + 1))
    (hfront : ResetLeftwardDigit ring G root j)
    (k : Nat) (hjk : j.val < k)
    (hkb : k ≤ (compileAdvice q).b) :
    (G.physical (site ring root (k - 1))).tok ≠ .IR := by
  by_cases he : k - 1 = j.val
  · intro hir
    have ht : (G.physical (site ring root j.val)).tok = .RL :=
      hfront.2.2.2
    have hs : site ring root (k - 1) = site ring root j.val :=
      congrArg (site ring root) he
    rw [hs, ht] at hir
    cases hir
  · have hmore : j.val < k - 1 := by omega
    have hs : SuffixClear ring G.physical root j.val :=
      (resetSuffixDigitIffOld ring G.physical root j).1
        (hsweep.2 j hfront)
    exact resetSuffixPrecludesIR ring G.physical root
      j.val (k - 1) hs hmore (by omega)

end Counter
end L3

/-!
Role-stable, grant-free, genuine-launch physical trial.

The physical phase is a property of C, not of ResetGhost marks.
The return is TERMINAL and is excluded from ResetTrialWord; the
post-state changes the root from RWAIT to ARMED.
GAP: ResetPhysicalRowClosure is deliberately a PROP, not an axiom
or theorem. The conditional history theorem below does not discharge
that row-closure obligation.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- A waiting root is physically in RWAIT with a positive lease. -/
def ResetRootWaiting {n q : Nat} (C : Config q n)
    (root : Fin n) : Prop :=
  (C root).mode = .RWAIT ∧ 0 < (C root).lease.val

/-- The immediately-post-genuine-RESET-launch physical facts.
No other digit, including the suffix, is restricted. -/
def ResetLaunchPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : Prop :=
  Complete ring C root ∧ GrantFree C root ∧
  1 ≤ (compileAdvice q).b ∧ ResetRootWaiting C root ∧
  (C (site ring root 1)).bit = false ∧
  (C (site ring root 1)).tok = .RR ∧
  (C root).lease.val = 13 * ((compileAdvice q).b + 2)

/-- An outward front has a zero/empty traversed prefix.
The untraversed suffix may contain arbitrary inherited garbage. -/
def ResetOutwardPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j : Nat) : Prop :=
  ResetRootWaiting C root ∧
  OutwardSnapshot ring C root j ∧
  (C (site ring root j)).bit = false

/-- The return front has a zero bit, and EVERY other active digit
(both prefix and suffix) has a zero bit and empty worker. -/
def ResetReturnPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j : Nat) : Prop :=
  ResetRootWaiting C root ∧
  LeftwardAt ring C root j ∧
  (C (site ring root j)).bit = false ∧
  (∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
    i ≠ j →
      (C (site ring root i)).bit = false ∧
      (C (site ring root i)).tok = .E)

/-- Physically observed newest launched front, before its terminal
root service. The two-phase strengthening excludes DESTROYED.
It is NOT asserted for arbitrary all-state configurations. -/
def ResetTrialPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : Prop :=
  (∃ j : Nat, ResetOutwardPhysical ring C root j) ∨
  (∃ j : Nat, ResetReturnPhysical ring C root j)

/-- Only role-stable, grant-free edges with a waiting positive-lease
root at the next cut are admitted. In particular the terminal RL
consumption is not part of this PRETERMINAL run. -/
def ResetTrialAllowed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) : Prop :=
  let D := (protocol q).step ring C e
  RoleStableEdge ring root C e ∧
    GrantFree C root ∧ GrantFree D root ∧
    ResetRootWaiting D root

/-- The entire actual-protocol edge word, with the stopping conditions
checked at EVERY intermediate cut, not just at the endpoints. -/
def ResetTrialWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Config q n → List (Fin n) → Prop
  | C, [] => GrantFree C root ∧ ResetRootWaiting C root
  | C, e :: w =>
      ResetTrialAllowed ring root C e ∧
      ResetTrialWord ring root ((protocol q).step ring C e) w

/-- The ONLY missing closure statement: all literal BANK cases,
including HOLDS, RR-over-collision, top-turn, RL-retreat,
IR/CR noninterference and wait/lease framing, must be lifted
through the real protocol. No proof is silently postulated. -/
def ResetPhysicalRowClosure {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (C : Config q n) (e : Fin n),
    Complete ring C root →
    ResetTrialPhysical ring C root →
    ResetTrialAllowed ring root C e →
    ResetTrialPhysical ring ((protocol q).step ring C e) root

theorem resetTrialStartOutward {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (h : ResetLaunchPhysical ring C root) :
    ResetTrialPhysical ring C root := by
  rcases h with ⟨_, _, hb, hw, hbit, htok, _⟩
  refine Or.inl ⟨1, ?_⟩
  refine ⟨hw, ?_, hbit⟩
  constructor
  · exact ⟨by omega, hb, htok⟩
  · intro i hi hlt
    omega

/-- In the outward phase, the newly launched physical RR is the
leftmost possible front: every earlier worker slot is literally E. -/
theorem resetOutwardPhysicalPrefix {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j i : Nat)
    (h : ResetOutwardPhysical ring C root j)
    (hi : 1 ≤ i) (hij : i < j) :
    (C (site ring root i)).bit = false ∧
    (C (site ring root i)).tok = .E :=
  h.2.1.2 i hi hij

/-- There cannot be two distinct outward positions with
cleared prefixes: the position is physically unique. -/
theorem resetOutwardPhysicalUnique {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j k : Nat)
    (hj : ResetOutwardPhysical ring C root j)
    (hk : ResetOutwardPhysical ring C root k) :
    j = k := by
  by_cases hlt : j < k
  · have he := (resetOutwardPhysicalPrefix ring C root k j
      hk hj.2.1.1.1 hlt).2
    have ht : (C (site ring root j)).tok = .RR :=
      hj.2.1.1.2.2
    rw [ht] at he
    cases he
  · by_cases hgt : k < j
    · have he := (resetOutwardPhysicalPrefix ring C root j k
        hj hk.2.1.1.1 hgt).2
      have ht : (C (site ring root k)).tok = .RR :=
        hk.2.1.1.2.2
      rw [ht] at he
      cases he
    · omega

theorem resetTrialWordRoleStable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config q n) (w : List (Fin n)),
      ResetTrialWord ring root C w →
      RoleStableWord ring root C w := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro _
      trivial
  | cons e es ih =>
      intro hw
      exact ⟨hw.1.1, ih _ hw.2⟩

theorem resetTrialWordGrantFree {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (C : Config q n) (w : List (Fin n)),
      ResetTrialWord ring root C w →
      GrantFree (Word ring w C) root := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro hw
      exact hw.1
  | cons e es ih =>
      intro hw
      exact ih _ hw.2

/-- Run induction is complete conditional on the stated
literal one-step BANK row theorem; no ghost invariant is used. -/
theorem resetTrialPhaseConditional {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : ResetPhysicalRowClosure (q := q) ring root) :
    ∀ (C : Config q n) (w : List (Fin n)),
      Complete ring C root →
      ResetTrialPhysical ring C root →
      ResetTrialWord ring root C w →
      ResetTrialPhysical ring (Word ring w C) root := by
  intro C w
  induction w generalizing C with
  | nil =>
      intro _ hp _
      exact hp
  | cons e es ih =>
      intro hc hp hw
      have hcnext : Complete ring
          ((protocol q).step ring C e) root := by
        intro j hj
        rw [hw.1.1 j hj]
        exact hc j hj
      have hpnext : ResetTrialPhysical ring
          ((protocol q).step ring C e) root :=
        hrows C e hc hp hw.1
      exact ih _ hcnext hpnext hw.2

/-- An RL at digit one in the physical two-phase class cannot be
an arbitrary inherited RL: the outward phase has an RR to its
right or at one; a return at a different position has cell one E. -/
theorem resetTrialReturnAtFirst {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (h : ResetTrialPhysical ring C root)
    (htok : (C (site ring root 1)).tok = .RL) :
    ResetReturnPhysical ring C root 1 := by
  rcases h with hout | hret
  · rcases hout with ⟨j, hj⟩
    by_cases hfirst : j = 1
    · subst j
      have hr : (C (site ring root 1)).tok = .RR :=
        hj.2.1.1.2.2
      rw [hr] at htok
      cases htok
    · have hlt : 1 < j := by
        have hp : 1 ≤ j := hj.2.1.1.1
        omega
      have he := (hj.2.1.2 1 (by omega) hlt).2
      rw [he] at htok
      cases htok
  · rcases hret with ⟨j, hj⟩
    by_cases hfirst : j = 1
    · simpa only [hfirst] using hj
    · have hne : 1 ≠ j := Ne.symm hfirst
      have hb : 1 ≤ (compileAdvice q).b :=
        Nat.le_trans hj.2.1.1 hj.2.1.2.1
      have he := (hj.2.2.2 1 (by omega) hb hne).2
      rw [he] at htok
      cases htok

/-- Reuse the terminal-row and suffix-frame theorems.
The return-phase premise gives their exact bit/worker hypotheses. -/
theorem resetTrialReturnTerminal {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hn : 2 ≤ n) (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hr : ResetReturnPhysical ring C root 1) :
    ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit = false ∧
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
  have hs : SuffixClear ring C root 1 := by
    intro i hi hb
    exact hr.2.2.2 i (by omega) hb (by omega)
  have hconsume := resetPhysicalRootConsumeRl
    ring C root hn hsp hr.2.1.2.1 hc hg
    hr.1.1 hr.2.1.2.2 hr.2.2.1
  exact resetFinalReturnOfClearedSuffix
    ring C root hc hs hconsume

/-- Appendix C(c) as a run theorem: the conclusion is for a
terminal root service AFTER a permitted nonterminal word.
GAP: hrows is not yet established from the literal BANK table. -/
theorem resetTrialPartCConditional {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (Czero : Config q n)
    (hn : 2 ≤ n) (hsp : (compileAdvice q).useSmall = false)
    (hlaunch : ResetLaunchPhysical ring Czero root)
    (hrows : ResetPhysicalRowClosure (q := q) ring root)
    (w : List (Fin n))
    (hw : ResetTrialWord ring root Czero w)
    (htok : ((Word ring w Czero)
      (site ring root 1)).tok = .RL) :
    ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (((protocol q).step ring (Word ring w Czero) root)
        (site ring root j)).bit = false ∧
      (((protocol q).step ring (Word ring w Czero) root)
        (site ring root j)).tok = .E := by
  have hp : ResetTrialPhysical ring (Word ring w Czero) root :=
    resetTrialPhaseConditional ring root hrows
      Czero w hlaunch.1
      (resetTrialStartOutward ring Czero root hlaunch) hw
  have hc : Complete ring (Word ring w Czero) root :=
    complete_word ring root w Czero hlaunch.1
      (resetTrialWordRoleStable ring root Czero w hw)
  have hg : GrantFree (Word ring w Czero) root :=
    resetTrialWordGrantFree ring root Czero w hw
  have hr : ResetReturnPhysical ring
      (Word ring w Czero) root 1 :=
    resetTrialReturnAtFirst ring
      (Word ring w Czero) root hp htok
  exact resetTrialReturnTerminal ring (Word ring w Czero)
    root hn hsp hc hg hr

end Counter
end L3

/-!
BANK frame and symbolic row certificates.

The all-edge ResetPhysicalRowClosure is NOT asserted. The current
theorems settle geometry, unrelated-edge preservation, and selected
literal BANK row groups. To establish closure, one must compose
them at every active-source edge (including the top/exterior seam),
incoming-root edge, and the SMALL branch.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- Ring geometry: successor has a unique predecessor.
This is independent of the BANK protocol and avoids assuming n>b. -/
theorem resetTrialNeighborInjective {n : Nat}
    (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

/-- If an edge's responder is an active digit j+1, its
initiator is the preceding digit j, even at the wrap seam. -/
theorem resetTrialSitePredecessor {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (j : Nat)
    (h : ring.rightNeighbor e = site ring root (j + 1)) :
    e = site ring root j := by
  apply resetTrialNeighborInjective ring
  change ring.rightNeighbor e =
    ring.rightNeighbor (site ring root j)
  exact h

/-- A physical edge starts inside the interval, enters its root,
or has both endpoints outside the entire interval. The root's
incoming edge is explicitly separated because the predecessor of
site zero is not required to be an active interval site. -/
theorem resetTrialEdgeGeometry {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    (∃ j : Nat, j ≤ (compileAdvice q).b ∧
      e = site ring root j) ∨
    ring.rightNeighbor e = root ∨
    OutsideSites q ring root e := by
  classical
  by_cases hs : ∃ j : Nat, j ≤ (compileAdvice q).b ∧
      e = site ring root j
  · exact Or.inl hs
  · by_cases hr : ring.rightNeighbor e = root
    · exact Or.inr (Or.inl hr)
    · apply Or.inr
      apply Or.inr
      intro j hj
      constructor
      · intro he
        exact hs ⟨j, hj, he⟩
      · intro he
        by_cases hz : j = 0
        · subst j
          have hroot : ring.rightNeighbor e = root := by
            simpa only [site] using he
          exact hr hroot
        · have hjpos : 0 < j := by omega
          have hjprev : j - 1 + 1 = j := by omega
          have htarget :
              ring.rightNeighbor e =
                site ring root (j - 1 + 1) := by
            rw [hjprev]
            exact he
          have hsource :=
            resetTrialSitePredecessor ring root e (j - 1) htarget
          exact hs ⟨j - 1, by omega, hsource⟩

/-- Congruence of the physical front predicate under equality of
all active interval Agents. No ghost or global-state closure. -/
theorem resetTrialPhysicalIntervalCongr {n q : Nat}
    (ring : DirectedRing n) (C D : Config q n)
    (root : Fin n)
    (hcell : ∀ i : Nat, i ≤ (compileAdvice q).b →
      D (site ring root i) = C (site ring root i))
    (hp : ResetTrialPhysical ring C root) :
    ResetTrialPhysical ring D root := by
  have hroot : D root = C root := by
    simpa only [site] using hcell 0 (by omega)
  rcases hp with hout | hret
  · rcases hout with ⟨j, hj⟩
    rcases hj with ⟨hw, ⟨ho, hprefix⟩, hbit⟩
    rcases ho with ⟨hjpos, hjbound, htok⟩
    refine Or.inl ⟨j, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · change (D root).mode = .RWAIT ∧
        0 < (D root).lease.val
      rw [hroot]
      exact hw
    · refine ⟨⟨hjpos, hjbound, ?_⟩, ?_⟩
      · simpa only [hcell j hjbound] using htok
      · intro i hi hij
        have hib : i ≤ (compileAdvice q).b := by omega
        simpa only [hcell i hib] using hprefix i hi hij
    · simpa only [hcell j hjbound] using hbit
  · rcases hret with ⟨j, hj⟩
    rcases hj with ⟨hw, hl, hbit, hclear⟩
    rcases hl with ⟨hjpos, hjbound, htok⟩
    refine Or.inr ⟨j, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (D root).mode = .RWAIT ∧
        0 < (D root).lease.val
      rw [hroot]
      exact hw
    · exact ⟨hjpos, hjbound,
        by simpa only [hcell j hjbound] using htok⟩
    · simpa only [hcell j hjbound] using hbit
    · intro i hi hib hneq
      simpa only [hcell i hib] using
        hclear i hi hib hneq

/-- Every fully exterior edge preserves the OUTWARD/RETURN phase.
This handles arbitrary inherited workers and exterior roles;
the FULL Agent, not merely BANK, is framed. -/
theorem resetTrialOutsidePreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hout : OutsideSites q ring root e)
    (hp : ResetTrialPhysical ring C root) :
    ResetTrialPhysical ring
      ((protocol q).step ring C e) root := by
  apply resetTrialPhysicalIntervalCongr ring C
    ((protocol q).step ring C e) root
  · exact outside_frame ring C root e hout
  · exact hp

/-- The real protocol's unselected agents retain all three BANK
coordinates, as a consequence of the full frame. -/
theorem resetTrialNonendpointBankFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (e i : Fin n)
    (hi : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    resetAgentBankTrip
      (((protocol q).step ring C e) i) =
    resetAgentBankTrip (C i) := by
  rw [step_frame ring C e i hi hj]

/-- Role stability of an allowed physical service preserves the
complete interval, including at an exterior-boundary service. -/
theorem resetTrialAllowedComplete {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (ha : ResetTrialAllowed ring root C e) :
    Complete ring ((protocol q).step ring C e) root := by
  intro j hj
  rw [ha.1 j hj]
  exact hc j hj

/-- Every physical phase has a genuine in-range digit position. -/
theorem resetTrialPhysicalHasDigit {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hp : ResetTrialPhysical ring C root) :
    1 ≤ (compileAdvice q).b := by
  rcases hp with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hf : OutwardAt ring C root j := hj.2.1.1
    exact Nat.le_trans hf.1 hf.2.1
  · have hf : LeftwardAt ring C root j := hj.2.1
    exact Nat.le_trans hf.1 hf.2.1

/-- A complete interval containing at least one active digit
forces at least two physical sites. This legitimizes the
selected-endpoint BANK projection for every trial phase. -/
theorem resetTrialMinRing {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root) :
    2 ≤ n := by
  by_cases hn : 2 ≤ n
  · exact hn
  · have hsmall : n = 1 := by
      have hpos := ring.hn
      omega
    have hb : 1 ≤ (compileAdvice q).b :=
      resetTrialPhysicalHasDigit ring C root hp
    have hd := resetCompleteSitesDifferent
      ring C root hc 1 0 hb (by omega) (by omega)
    have hsame : site ring root 1 = site ring root 0 := by
      apply Fin.ext
      change (root.val + 1) % n = root.val
      have hrval : root.val = 0 := by
        have hlt := root.isLt
        omega
      simp [hsmall, hrval]
    exact False.elim (hd hsame)

/-- The selected-source/responder BANK trip is that of literal
bankPair on the OLD cells. The distinct-endpoint premise of
resetPhysicalEdgeBankTrip is discharged from trial geometry. -/
theorem resetTrialSelectedBankTrip {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false) :
    resetAgentBankTrip (((protocol q).step ring C e) e) =
        resetCellBankTrip (resetBankOld
          (C e) (C (ring.rightNeighbor e))).1 ∧
    resetAgentBankTrip
        (((protocol q).step ring C e)
          (ring.rightNeighbor e)) =
        resetCellBankTrip (resetBankOld
          (C e) (C (ring.rightNeighbor e))).2 := by
  have hn : 2 ≤ n := resetTrialMinRing ring C root hc hp
  exact resetPhysicalEdgeBankTrip ring C e
    (resetRootPortDistinct ring e hn) hsp

/-! ### Symbolic BANK owner: matched active consecutive digits.

In each lemma below the BANK token/bit equations are concluded from
the literal first-match guards, not from a surrogate automaton.
All other inherited contents (unless explicitly constrained) remain
arbitrary. These are pure bankPair rows, still requiring the spatial
projection and ring-case assembly for ResetPhysicalRowClosure. -/

/-- Row 154-155: the OUTWARD RR source has first-match priority over
an arbitrary destination worker and zeroes the destination bit. -/
theorem resetTrialBankForwardSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .RR) (hbx : x.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .E ∧ z.1.bit = false ∧
      z.2.tok = .RR ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  by_cases htop : y.role = b
  · by_cases hir : y.tok = .IR
    · simp [bankPair, hxne, hyne, hx, hlt, hxle,
        hy, hyle, hypos, hxb, htx, hbx, htop, hir]
    · simp [bankPair, hxne, hyne, hx, hlt, hxle,
        hy, hyle, hypos, hxb, htx, hbx, htop, hir]
  · simp [bankPair, hxne, hyne, hx, hlt, hxle,
      hy, hyle, hypos, hxb, htx, hbx, htop]

/-- Row 156-157: an RR at the top turns into RL on its
predecessor; the old top bit must already be cleared. -/
theorem resetTrialBankTopTurnSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (htx : x.tok = .E) (hty : y.tok = .RR)
    (hby : y.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .RL ∧ z.1.bit = false ∧
      z.2.tok = .E ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  have hxtop : x.role + 1 = b := by omega
  have hb0 : b ≠ 0 := by omega
  simp [bankPair, hxne, hyne, hx, hlt, hxle,
    hy, hyle, hypos, hxb, htop, htx, hty, hby, hnlt, hxtop, hb0]

/-- Row 158-159: returning RL overwrites the predecessor and
clears its own source; the suffix stays zero/empty. -/
theorem resetTrialBankRetreatSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .RL)
    (hby : y.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .RL ∧ z.1.bit = false ∧
      z.2.tok = .E ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  simp [bankPair, hxne, hyne, hx, hlt, hxle,
    hy, hyle, hypos, hxb, htx, hty, hby, hnlt]

/-- BANK HOLDS: an already-swept internal empty pair cannot
generate an IR or CR writer (nor any other worker). -/
theorem resetTrialBankEmptyHoldsSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .E)
    (hbx : x.bit = false) (hby : y.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .E ∧ z.1.bit = false ∧
      z.2.tok = .E ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  simp [bankPair, hxne, hyne, hx, hlt, hxle,
    hy, hyle, hypos, hxb, htx, hty, hbx, hby]

/-- BANK HOLDS: a swept predecessor cannot prematurely change
an outward RR at a non-top digit. -/
theorem resetTrialBankPredecessorHoldsSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) (hyn : y.role < b)
    (htx : x.tok = .E) (hty : y.tok = .RR)
    (hbx : x.bit = false) (hby : y.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .E ∧ z.1.bit = false ∧
      z.2.tok = .RR ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hynb : y.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  have hntop : x.role + 1 ≠ b := by omega
  simp [bankPair, hxne, hyne, hx, hlt, hxle,
    hy, hyle, hypos, hxb, hynb, htx, hty, hbx, hby, hnlt, hntop]

/-- Root wait on an empty digit one (the cleared prefix of any
outward/return phase with front position greater than one). -/
theorem resetTrialBankRootWaitEmptySymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RWAIT)
    (hb : 1 < b)
    (ht : y.tok = .E) (hbit : y.bit = false) :
    let z := bankPair x y 1 b theta
    z.2.tok = .E ∧ z.2.bit = false := by
  have hbge : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  simp [bankPair, hr, hg, hy, hm, hbge, hbne,
    ht, hbit, isRetTok]

/-- Root wait on RR at digit one. For spatial b>1, this is
a pure wait/lease step; b=1 has a separate RR-to-RL rule. -/
theorem resetTrialBankRootWaitOutwardSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RWAIT)
    (hb : 1 < b)
    (ht : y.tok = .RR) (hbit : y.bit = false) :
    let z := bankPair x y 1 b theta
    z.2.tok = .RR ∧ z.2.bit = false := by
  have hbge : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  simp [bankPair, hr, hg, hy, hm, hbge, hbne,
    ht, hbit, isRetTok]

end Counter
end L3

/-!
Additional whole-protocol edge families.
The spatial active-front assembly, hence ResetPhysicalRowClosure, is open.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- Every compiled BANK width is >1, including SMALL. -/
theorem resetTrialCompiledWidth (q : Nat) :
    1 < (compileAdvice q).b := by
  change 1 < paddedS (sourceTOfQ q) + 11
  omega

/-- Root waiting plus equality of all active digit bits/tokens
suffices to transport either physical phase. -/
theorem resetTrialPhysicalDigitsCongr {n q : Nat}
    (ring : DirectedRing n)
    (C D : Config q n) (root : Fin n)
    (hw : ResetRootWaiting D root)
    (hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit = (C (site ring root i)).bit ∧
      (D (site ring root i)).tok = (C (site ring root i)).tok)
    (hp : ResetTrialPhysical ring C root) :
    ResetTrialPhysical ring D root := by
  rcases hp with hout | hret
  · rcases hout with ⟨j, hj⟩
    rcases hj with ⟨_, ⟨⟨hjpos, hjbound, htok⟩, hprefix⟩, hbit⟩
    refine Or.inl ⟨j, ?_⟩
    refine ⟨hw, ?_, ?_⟩
    · refine ⟨⟨hjpos, hjbound, ?_⟩, ?_⟩
      · exact ((hf j hjpos hjbound).2).trans htok
      · intro i hi hij
        have hib : i ≤ (compileAdvice q).b := by omega
        have hh := hf i hi hib
        have hc := hprefix i hi hij
        exact ⟨hh.1.trans hc.1, hh.2.trans hc.2⟩
    · exact ((hf j hjpos hjbound).1).trans hbit
  · rcases hret with ⟨j, hj⟩
    rcases hj with ⟨_, ⟨hjpos, hjbound, htok⟩, hbit, hclear⟩
    refine Or.inr ⟨j, ?_⟩
    refine ⟨hw, ?_, ?_, ?_⟩
    · exact ⟨hjpos, hjbound,
        ((hf j hjpos hjbound).2).trans htok⟩
    · exact ((hf j hjpos hjbound).1).trans hbit
    · intro i hi hib hneq
      have hh := hf i hi hib
      have hc := hclear i hi hib hneq
      exact ⟨hh.1.trans hc.1, hh.2.trans hc.2⟩

/-- Neither endpoint of an edge strictly ahead of the outward
front touches a digit at or behind the front, even at ring wrap. -/
theorem resetTrialAheadEndpointsAvoid {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (j k i : Nat)
    (hi : 1 ≤ i) (hij : i ≤ j)
    (hjk : j < k) (hkb : k ≤ (compileAdvice q).b) :
    site ring root i ≠ site ring root k ∧
    site ring root i ≠
      ring.rightNeighbor (site ring root k) := by
  have hib : i ≤ (compileAdvice q).b := by omega
  have hneq : i ≠ k := by omega
  constructor
  · exact resetCompleteSitesDifferent ring C root hc i k hib hkb
      hneq
  · intro heq
    have hp : i - 1 + 1 = i := by omega
    have hsource :
        ring.rightNeighbor (site ring root (i - 1)) =
        ring.rightNeighbor (site ring root k) := by
      calc
        ring.rightNeighbor (site ring root (i - 1)) =
            site ring root (i - 1 + 1) := rfl
        _ = site ring root i := by rw [hp]
        _ = ring.rightNeighbor (site ring root k) := heq
    have hsame : site ring root (i - 1) = site ring root k :=
      resetTrialNeighborInjective ring hsource
    have hdiff : site ring root (i - 1) ≠ site ring root k :=
      resetCompleteSitesDifferent ring C root hc (i - 1) k
        (by omega) hkb (by omega)
    exact hdiff hsame

/-- Abstract outward preservation when all digit sites 1..j
are framed; the next-cut lease condition is not forgotten. -/
theorem resetTrialOutwardFrontFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (j : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C e)
    (hf : ∀ i : Nat, 1 ≤ i → i ≤ j →
      ((protocol q).step ring C e) (site ring root i) =
        C (site ring root i)) :
    ResetOutwardPhysical ring
      ((protocol q).step ring C e) root j := by
  rcases hout with ⟨_, ⟨⟨hjpos, hjbound, htok⟩, hprefix⟩, hbit⟩
  refine ⟨ha.2.2.2, ?_, ?_⟩
  · refine ⟨⟨hjpos, hjbound, ?_⟩, ?_⟩
    · simpa only [hf j hjpos (by omega)] using htok
    · intro i hi hij
      have hle : i ≤ j := by omega
      simpa only [hf i hi hle] using hprefix i hi hij
  · simpa only [hf j hjpos (by omega)] using hbit

/-- Full-protocol preservation for an edge ahead of OUTWARD(j).
This includes the k=b top/exterior or root-wrapping seam. -/
theorem resetTrialAheadPreservesOutward {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (j k : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C (site ring root k))
    (hjk : j < k) (hkb : k ≤ (compileAdvice q).b) :
    ResetOutwardPhysical ring
      ((protocol q).step ring C (site ring root k)) root j := by
  apply resetTrialOutwardFrontFrame ring C root
    (site ring root k) j hout ha
  intro i hi hij
  have havoid := resetTrialAheadEndpointsAvoid
    ring C root hc j k i hi hij hjk hkb
  exact step_frame ring C (site ring root k)
    (site ring root i) havoid.1 havoid.2

theorem resetTrialAheadPreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (j k : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C (site ring root k))
    (hjk : j < k) (hkb : k ≤ (compileAdvice q).b) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  exact Or.inl ⟨j, resetTrialAheadPreservesOutward
    ring C root hc j k hout ha hjk hkb⟩

/-- If the edge enters the root from outside the active digits,
only the root can change among sites zero..b. Next-cut RWAIT
is supplied by ResetTrialAllowed. -/
theorem resetTrialIncomingRootExterior {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (ha : ResetTrialAllowed ring root C e)
    (hy : ring.rightNeighbor e = root)
    (hex : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b → e ≠ site ring root i) :
    ResetTrialPhysical ring
      ((protocol q).step ring C e) root := by
  apply resetTrialPhysicalDigitsCongr ring C
    ((protocol q).step ring C e) root ha.2.2.2 ?_ hp
  intro i hi hib
  have hr : site ring root i ≠ root := by
    change site ring root i ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc i 0 hib
      (by omega) (by omega)
  have hnoty : site ring root i ≠ ring.rightNeighbor e := by
    intro he
    apply hr
    calc
      site ring root i = ring.rightNeighbor e := he
      _ = root := hy
  have hnotx : site ring root i ≠ e :=
    Ne.symm (hex i hi hib)
  have hh := step_frame ring C e (site ring root i) hnotx hnoty
  constructor
  · exact congrArg
      (fun a : Agent (compileAdvice q) => a.bit) hh
  · exact congrArg
      (fun a : Agent (compileAdvice q) => a.tok) hh

/-- Strictly within the outward swept prefix, both worker slots
and bits are empty; no ordinary collision or IR writer is possible. -/
theorem resetTrialOutwardSweptPairEmpty {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j k : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (hk : 1 ≤ k) (hkj : k + 1 < j) :
    (C (site ring root k)).bit = false ∧
    (C (site ring root k)).tok = .E ∧
    (C (site ring root (k + 1))).bit = false ∧
    (C (site ring root (k + 1))).tok = .E := by
  have hp := hout.2.1.2
  have hx := hp k hk (by omega)
  have hy := hp (k + 1) (by omega) hkj
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- The predecessor of a noninitial outward RR is empty. -/
theorem resetTrialOutwardFrontPredecessorEmpty {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (hj : 1 < j) :
    (C (site ring root (j - 1))).bit = false ∧
      (C (site ring root (j - 1))).tok = .E := by
  exact hout.2.1.2 (j - 1) (by omega) (by omega)

/-- At most one active return worker; collision row 160-165
cannot have two nonempty adjacent internal operands. -/
theorem resetTrialReturnNoAdjacentCollision {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j k : Nat)
    (hret : ResetReturnPhysical ring C root j)
    (hk : 1 ≤ k) (hkb : k + 1 ≤ (compileAdvice q).b) :
    ¬ ((C (site ring root k)).tok ≠ .E ∧
        (C (site ring root (k + 1))).tok ≠ .E) := by
  intro hbad
  by_cases hj : k = j
  · have hn : k + 1 ≠ j := by omega
    have hclear := hret.2.2.2 (k + 1)
      (by omega) hkb hn
    exact hbad.2 hclear.2
  · have hclear := hret.2.2.2 k hk (by omega) hj
    exact hbad.1 hclear.2

/-- All four BANK coordinates; the SMALL owner cannot write them. -/
def resetTrialBankFields {c : Compiled} (a : Agent c) :
    Mode × Bool × BTok × Fin (c.bankLeaseCap + 1) :=
  (a.mode, a.bit, a.tok, a.lease)

/-- SMALL Base writes only SMALL and later non-BANK fields. -/
theorem resetTrialBaseSmallFields (c : Compiled)
    (ev : CertEvent) (x y : Agent c)
    (hs : c.useSmall = true) :
    resetTrialBankFields (baseStep c ev x y).1 =
      resetTrialBankFields x ∧
    resetTrialBankFields (baseStep c ev x y).2 =
      resetTrialBankFields y := by
  constructor
  · simp [resetTrialBankFields, baseStep, hs,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | rfl | split)
  · simp [resetTrialBankFields, baseStep, hs,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | rfl | split)

/-- Full transition retains SMALL Base's BANK coordinates. -/
theorem resetTrialTransitionSmallFields (c : Compiled)
    (x y : Agent c) (hs : c.useSmall = true) :
    resetTrialBankFields (transition c x y).1 =
      resetTrialBankFields x ∧
    resetTrialBankFields (transition c x y).2 =
      resetTrialBankFields y := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := resetTrialBaseSmallFields c ev x y hs
  simpa [transition, hc, hh, resetTrialBankFields,
    assemble] using hb

/-- SMALL preserves BANK on every site for a ring of size >=2. -/
theorem resetTrialSmallFieldsEverySite {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (e i : Fin n) (hn : 2 ≤ n)
    (hs : (compileAdvice q).useSmall = true) :
    resetTrialBankFields (((protocol q).step ring C e) i) =
      resetTrialBankFields (C i) := by
  have hh := resetTrialTransitionSmallFields (compileAdvice q)
    (C e) (C (ring.rightNeighbor e)) hs
  by_cases hi : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol] using hh.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hne : ring.rightNeighbor e ≠ e :=
        resetRootPortDistinct ring e hn
      simpa [PopulationProtocol.step, protocol, hne] using hh.2
    · exact congrArg
        (fun a : Agent (compileAdvice q) => resetTrialBankFields a)
        (step_frame ring C e i hi hj)

/-- Entire SMALL mode is phase-preserving, no BANK row splitting. -/
theorem resetTrialSmallPhysicalClosure {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hs : (compileAdvice q).useSmall = true) :
    ∀ (C : Config q n) (e : Fin n),
      Complete ring C root →
      ResetTrialPhysical ring C root →
      ResetTrialAllowed ring root C e →
      ResetTrialPhysical ring ((protocol q).step ring C e) root := by
  intro C e hc hp ha
  have hn : 2 ≤ n := resetTrialMinRing ring C root hc hp
  apply resetTrialPhysicalDigitsCongr ring C
    ((protocol q).step ring C e) root ha.2.2.2 ?_ hp
  intro i hi hib
  have h := resetTrialSmallFieldsEverySite ring C e
    (site ring root i) hn hs
  constructor
  · exact congrArg
      (fun z : Mode × Bool × BTok ×
        Fin ((compileAdvice q).bankLeaseCap + 1) => z.2.1) h
  · exact congrArg
      (fun z : Mode × Bool × BTok ×
        Fin ((compileAdvice q).bankLeaseCap + 1) => z.2.2.1) h

end Counter
end L3
/-!
Positional BANK assembly, partial.

The selected-edge bridge is used below for the forward, top-turn,
retreat, and empty/empty internal rows. Root-outgoing and the complete
spatial edge cover remain open; no unconditional ResetPhysicalRowClosure
is asserted.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- Match the real protocol's selected endpoints with the literal
bankPair for a consecutive complete-role edge, including k=0.
No equality of entire Agents is claimed. -/
theorem resetTrialConsecutiveBankTrip {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : k < (compileAdvice q).b) :
    let x := site ring root k
    let y := site ring root (k + 1)
    let bx := bankCell (C x) k
    let byy := bankCell (C y) (k + 1)
    let z := bankPair bx byy (k + 1)
      (compileAdvice q).b (compileAdvice q).theta
    let D := (protocol q).step ring C x
    resetAgentBankTrip (D x) = resetCellBankTrip z.1 ∧
      resetAgentBankTrip (D y) = resetCellBankTrip z.2 := by
  have hxrole :
      (C (site ring root k)).pack.val = k :=
    hc k (by omega)
  have hyrole :
      (C (site ring root (k + 1))).pack.val = k + 1 :=
    hc (k + 1) (by omega)
  have hpack : packNext k (k + 1) (compileAdvice q).b =
      k + 1 := by
    simp [packNext, hk]
  have h := resetTrialSelectedBankTrip ring C root
    (site ring root k) hc hp hsp
  change
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root k))
          (site ring root k)) =
        resetCellBankTrip
          (resetBankOld
            (C (site ring root k))
            (C (site ring root (k + 1)))).1 ∧
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root k))
          (site ring root (k + 1))) =
        resetCellBankTrip
          (resetBankOld
            (C (site ring root k))
            (C (site ring root (k + 1)))).2 at h
  simpa only [resetBankOld, hxrole, hyrole, hpack] using h

/-- Forget the mode component of a selected BANK triple. -/
theorem resetTrialTripBitTok {c : Compiled}
    (a : Agent c) (z : BankCell)
    (h : resetAgentBankTrip a = resetCellBankTrip z) :
    a.bit = z.bit ∧ a.tok = z.tok := by
  constructor
  · exact congrArg
      (fun v : Mode × Bool × BTok => v.2.1) h
  · exact congrArg
      (fun v : Mode × Bool × BTok => v.2.2) h

/-- General endpoint custody for any literal BANK row with
specified output bit and worker token. This handles the actual
Protocol.step, not a replacement BANK-only transition. -/
theorem resetTrialSelectedRowFields {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : k < (compileAdvice q).b)
    (tx ty : BTok) (vx vy : Bool)
    (hrow :
      let x := site ring root k
      let y := site ring root (k + 1)
      let bx := bankCell (C x) k
      let byy := bankCell (C y) (k + 1)
      let z := bankPair bx byy (k + 1)
        (compileAdvice q).b (compileAdvice q).theta
      z.1.tok = tx ∧ z.1.bit = vx ∧
        z.2.tok = ty ∧ z.2.bit = vy) :
    let x := site ring root k
    let y := site ring root (k + 1)
    let D := (protocol q).step ring C x
    (D x).bit = vx ∧ (D x).tok = tx ∧
      (D y).bit = vy ∧ (D y).tok = ty := by
  let x := site ring root k
  let y := site ring root (k + 1)
  let bx := bankCell (C x) k
  let byy := bankCell (C y) (k + 1)
  let z := bankPair bx byy (k + 1)
    (compileAdvice q).b (compileAdvice q).theta
  let D := (protocol q).step ring C x
  have hpairs :
      resetAgentBankTrip (D x) = resetCellBankTrip z.1 ∧
      resetAgentBankTrip (D y) = resetCellBankTrip z.2 :=
    resetTrialConsecutiveBankTrip ring C root hc hp hsp k hk
  have hs := resetTrialTripBitTok (D x) z.1 hpairs.1
  have ht := resetTrialTripBitTok (D y) z.2 hpairs.2
  exact ⟨hs.1.trans hrow.2.1, hs.2.trans hrow.1,
    ht.1.trans hrow.2.2.2, ht.2.trans hrow.2.2.1⟩

/-- Case A, row 154-155: the real selected edge at OUTWARD(j)
advances the RR by one digit, zeroing the destination and
emptying the source, regardless of inherited destination garbage.
This also covers the advance INTO the top digit. -/
theorem resetTrialOutwardAdvance {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hout : ResetOutwardPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C (site ring root j))
    (hj : j < (compileAdvice q).b) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root j)) root := by
  let bx := bankCell (C (site ring root j)) j
  let byy := bankCell (C (site ring root (j + 1))) (j + 1)
  have hjpos : 1 ≤ j := hout.2.1.1.1
  have hxpos : 1 ≤ bx.role := by
    change 1 ≤ j
    exact hjpos
  have hxlt : bx.role < (compileAdvice q).b := by
    change j < (compileAdvice q).b
    exact hj
  have hy : byy.role = bx.role + 1 := rfl
  have htok : bx.tok = .RR := by
    change (C (site ring root j)).tok = .RR
    exact hout.2.1.1.2.2
  have hbit : bx.bit = false := by
    change (C (site ring root j)).bit = false
    exact hout.2.2
  have howner := resetTrialBankForwardSymbolic bx byy
    (compileAdvice q).b (compileAdvice q).theta
    hxpos hxlt hy htok hbit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inl ⟨j, hout⟩) hsp j hj .E .RR false false howner
  refine Or.inl ⟨j + 1, ?_⟩
  refine ⟨ha.2.2.2, ?_, hpair.2.2.1⟩
  · refine ⟨⟨by omega, by omega, hpair.2.2.2⟩, ?_⟩
    intro i hi hij
    by_cases he : i = j
    · subst i
      exact ⟨hpair.1, hpair.2.1⟩
    · have hbefore : i < j := by omega
      have hnotx : site ring root i ≠ site ring root j :=
        resetCompleteSitesDifferent ring C root hc i j
          (by omega) (by omega) (by omega)
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root j) := by
        change site ring root i ≠ site ring root (j + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (j + 1) (by omega) (by omega) (by omega)
      have hframe := step_frame ring C
        (site ring root j) (site ring root i) hnotx hnoty
      simpa only [hframe] using hout.2.1.2 i hi hbefore

/-- Case B, row 156-157: once RR sits at digit b, service of
(b-1,b) turns it into RETURN(b-1); all other active digits
are zero and empty afterward. -/
theorem resetTrialOutwardTopTurn {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hout : ResetOutwardPhysical ring C root (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C
      (site ring root ((compileAdvice q).b - 1))) :
    ResetTrialPhysical ring
      ((protocol q).step ring C
        (site ring root ((compileAdvice q).b - 1))) root := by
  let b := (compileAdvice q).b
  let k := b - 1
  have hb : 1 < b := resetTrialCompiledWidth q
  have hkpos : 1 ≤ k := by dsimp [k]; omega
  have hklt : k < b := by dsimp [k]; omega
  have hkadd : k + 1 = b := by dsimp [k]; omega
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hpre := hout.2.1.2 k hkpos (by omega)
  have hsource : bx.tok = .E := by
    change (C (site ring root k)).tok = .E
    exact hpre.2
  have htop : byy.role = b := by
    change k + 1 = b
    exact hkadd
  have htarget : byy.tok = .RR := by
    change (C (site ring root (k + 1))).tok = .RR
    rw [hkadd]
    exact hout.2.1.1.2.2
  have htargetBit : byy.bit = false := by
    change (C (site ring root (k + 1))).bit = false
    rw [hkadd]
    exact hout.2.2
  have howner := resetTrialBankTopTurnSymbolic bx byy
    b (compileAdvice q).theta
    (by change 1 ≤ k; exact hkpos)
    (by change k < b; exact hklt)
    (by rfl) htop hsource htarget htargetBit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inl ⟨b, hout⟩) hsp k hklt .RL .E false false howner
  refine Or.inr ⟨k, ?_⟩
  refine ⟨ha.2.2.2, ?_, hpair.1, ?_⟩
  · exact ⟨hkpos, by omega, hpair.2.1⟩
  · intro i hi hib hneq
    by_cases hitop : i = k + 1
    · subst i
      exact ⟨hpair.2.2.1, hpair.2.2.2⟩
    · have hbefore : i < k := by omega
      have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hneq
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib (by omega) hitop
      have hframe :
          ((protocol q).step ring C
            (site ring root ((compileAdvice q).b - 1)))
            (site ring root i) = C (site ring root i) :=
        step_frame ring C (site ring root k)
          (site ring root i) hnotx hnoty
      rw [hframe]
      exact hout.2.1.2 i hi (by omega)

/-- Case C, row 158-159: an authentic RL at digit k+1 moves
to digit k, with every other active digit zero and empty.
In particular k=1 is a VALID retreat, not the terminal root
consumption; terminal is the later edge at site zero. -/
theorem resetTrialReturnRetreat {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hret : ResetReturnPhysical ring C root (k + 1))
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  let b := (compileAdvice q).b
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hclear := hret.2.2.2 k hk (by omega) (by omega)
  have hsource : bx.tok = .E := by
    change (C (site ring root k)).tok = .E
    exact hclear.2
  have htarget : byy.tok = .RL := by
    change (C (site ring root (k + 1))).tok = .RL
    exact hret.2.1.2.2
  have htargetBit : byy.bit = false := by
    change (C (site ring root (k + 1))).bit = false
    exact hret.2.2.1
  have howner := resetTrialBankRetreatSymbolic bx byy
    b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < b; omega)
    (by rfl) hsource htarget htargetBit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inr ⟨k + 1, hret⟩) hsp
    k (by omega) .RL .E false false howner
  refine Or.inr ⟨k, ?_⟩
  refine ⟨ha.2.2.2, ?_, hpair.1, ?_⟩
  · exact ⟨hk, by omega, hpair.2.1⟩
  · intro i hi hib hneq
    by_cases hy : i = k + 1
    · subst i
      exact ⟨hpair.2.2.1, hpair.2.2.2⟩
    · have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hneq
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib hkb hy
      have hframe := step_frame ring C (site ring root k)
        (site ring root i) hnotx hnoty
      simpa only [hframe] using hret.2.2.2 i hi hib hy

/-- Case D, internal E/E zero pair: no worker is minted, and the
phase survives because the pair's two fields are unchanged and
all other active digit sites are fully framed. -/
theorem resetTrialEmptyInternalPreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hp : ResetTrialPhysical ring C root)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hleft :
      (C (site ring root k)).bit = false ∧
      (C (site ring root k)).tok = .E)
    (hright :
      (C (site ring root (k + 1))).bit = false ∧
      (C (site ring root (k + 1))).tok = .E)
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  let b := (compileAdvice q).b
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have howner := resetTrialBankEmptyHoldsSymbolic bx byy
    b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < b; omega)
    (by rfl)
    (by change (C (site ring root k)).tok = .E; exact hleft.2)
    (by change (C (site ring root (k + 1))).tok = .E;
        exact hright.2)
    (by change (C (site ring root k)).bit = false; exact hleft.1)
    (by change (C (site ring root (k + 1))).bit = false;
        exact hright.1)
  have hpair := resetTrialSelectedRowFields ring C root hc
    hp hsp k (by omega) .E .E false false howner
  apply resetTrialPhysicalDigitsCongr ring C
    ((protocol q).step ring C (site ring root k))
    root ha.2.2.2 ?_ hp
  intro i hi hib
  by_cases hsource : i = k
  · subst i
    constructor
    · exact hpair.1.trans hleft.1.symm
    · exact hpair.2.1.trans hleft.2.symm
  · by_cases htarget : i = k + 1
    · subst i
      constructor
      · exact hpair.2.2.1.trans hright.1.symm
      · exact hpair.2.2.2.trans hright.2.symm
    · have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hsource
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib hkb htarget
      have hframe := step_frame ring C (site ring root k)
        (site ring root i) hnotx hnoty
      constructor
      · exact congrArg
          (fun a : Agent (compileAdvice q) => a.bit) hframe
      · exact congrArg
          (fun a : Agent (compileAdvice q) => a.tok) hframe

end Counter
end L3
/-!
Exact root-outgoing RWAIT service.
The spatial all-edge cover and general RowClosure remain open.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- In the spatial RWAIT row, an empty or RR digit one is not
written. The source of the conclusion is the actual Protocol.step
endpoint projection, not a BANK-only replacement transition. -/
theorem resetTrialRootOutWaitFields {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetTrialAllowed ring root C root)
    (hw : ResetRootWaiting C root)
    (hbit : (C (site ring root 1)).bit = false)
    (htok : (C (site ring root 1)).tok = .E ∨
      (C (site ring root 1)).tok = .RR) :
    let D := (protocol q).step ring C root
    (D (site ring root 1)).bit =
        (C (site ring root 1)).bit ∧
      (D (site ring root 1)).tok =
        (C (site ring root 1)).tok := by
  let bx := bankCell (C root) 0
  let byy := bankCell (C (site ring root 1)) 1
  let z := bankPair bx byy 1 (compileAdvice q).b
    (compileAdvice q).theta
  let D := (protocol q).step ring C root
  have hb : 1 < (compileAdvice q).b :=
    resetTrialCompiledWidth q
  have hroot : bx.role = 0 := rfl
  have hgrant : bx.grant = false := ha.2.1
  have hfirst : byy.role = 1 := rfl
  have hmode : bx.mode = .RWAIT := hw.1
  have hkeep : z.2.tok = byy.tok ∧
      z.2.bit = byy.bit := by
    rcases htok with he | hr
    · have he' : byy.tok = .E := he
      have hrw := resetTrialBankRootWaitEmptySymbolic
        bx byy (compileAdvice q).b (compileAdvice q).theta
        hroot hgrant hfirst hmode hb he' hbit
      exact ⟨hrw.1.trans he'.symm, hrw.2.trans hbit.symm⟩
    · have hr' : byy.tok = .RR := hr
      have hrw := resetTrialBankRootWaitOutwardSymbolic
        bx byy (compileAdvice q).b (compileAdvice q).theta
        hroot hgrant hfirst hmode hb hr' hbit
      exact ⟨hrw.1.trans hr'.symm, hrw.2.trans hbit.symm⟩
  have hproj :
      resetAgentBankTrip (D (site ring root 1)) =
        resetCellBankTrip z.2 :=
    (resetTrialConsecutiveBankTrip ring C root hc hp hsp
      0 (by omega)).2
  have hf := resetTrialTripBitTok
    (D (site ring root 1)) z.2 hproj
  exact ⟨hf.1.trans hkeep.2, hf.2.trans hkeep.1⟩

/-- Every digit other than digit one is fully framed on a root
outgoing service, because the complete PACK roles distinguish
the selected endpoints from all other active digits. -/
theorem resetTrialRootOutOtherDigitsFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (i : Nat) (hi : 2 ≤ i)
    (hib : i ≤ (compileAdvice q).b) :
    ((protocol q).step ring C root) (site ring root i) =
      C (site ring root i) := by
  have hzero : site ring root i ≠ root := by
    change site ring root i ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      i 0 hib (by omega) (by omega)
  have hone : site ring root i ≠ ring.rightNeighbor root := by
    change site ring root i ≠ site ring root 1
    exact resetCompleteSitesDifferent ring C root hc
      i 1 hib (by omega) (by omega)
  exact step_frame ring C root (site ring root i) hzero hone

/-- Root outgoing while waiting does not disturb an outward or
returning physical front unless the root consumes an RL at one.
This lemma handles the E/RR alternatives; the RL alternative
is excluded by the separate exact mode certificate below. -/
theorem resetTrialRootOutWaitPreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetTrialAllowed ring root C root)
    (hw : ResetRootWaiting C root)
    (hbit : (C (site ring root 1)).bit = false)
    (htok : (C (site ring root 1)).tok = .E ∨
      (C (site ring root 1)).tok = .RR) :
    ResetTrialPhysical ring
      ((protocol q).step ring C root) root := by
  have hone := resetTrialRootOutWaitFields
    ring C root hc hp hsp ha hw hbit htok
  apply resetTrialPhysicalDigitsCongr ring C
    ((protocol q).step ring C root) root ha.2.2.2 ?_ hp
  intro i hi hib
  by_cases hfirst : i = 1
  · subst i
    exact hone
  · have hlarge : 2 ≤ i := by omega
    have hframe := resetTrialRootOutOtherDigitsFrame
      ring C root hc i hlarge hib
    constructor
    · exact congrArg
        (fun a : Agent (compileAdvice q) => a.bit) hframe
    · exact congrArg
        (fun a : Agent (compileAdvice q) => a.tok) hframe

/-- The terminal RWAIT/RL row changes the PHYSICAL root mode
to ARMED, not merely the responder's worker token. -/
theorem resetTrialRootRlArms {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hw : ResetRootWaiting C root)
    (hg : GrantFree C root)
    (hbit : (C (site ring root 1)).bit = false)
    (htok : (C (site ring root 1)).tok = .RL) :
    (((protocol q).step ring C root) root).mode = .ARMED := by
  let bx := bankCell (C root) 0
  let byy := bankCell (C (site ring root 1)) 1
  let z := bankPair bx byy 1 (compileAdvice q).b
    (compileAdvice q).theta
  have hbank : z.1.mode = .ARMED :=
    (resetBankConsumeRl bx byy
      (compileAdvice q).b (compileAdvice q).theta
      (by rfl) hg (by rfl) hw.1 htok hbit
      (by have hb := resetTrialCompiledWidth q; omega)).1
  have htriple :
      resetAgentBankTrip
        (((protocol q).step ring C root) root) =
      resetCellBankTrip z.1 :=
    (resetTrialConsecutiveBankTrip ring C root hc hp hsp
      0 (by have hb := resetTrialCompiledWidth q; omega)).1
  have hmode := congrArg
    (fun v : Mode × Bool × BTok => v.1) htriple
  change (((protocol q).step ring C root) root).mode =
      z.1.mode at hmode
  exact hmode.trans hbank

/-- A certified RETURN(1) cannot be consumed inside the
preterminal ResetTrialAllowed relation, because ARMED is not
RWAIT. This explicitly excludes the actual root service. -/
theorem resetTrialRootRlTerminalExcluded {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hret : ResetReturnPhysical ring C root 1) :
    ¬ ResetTrialAllowed ring root C root := by
  intro ha
  have hmode : (((protocol q).step ring C root) root).mode =
      .ARMED :=
    resetTrialRootRlArms ring C root hc
      (Or.inr ⟨1, hret⟩) hsp hret.1 ha.2.1
      hret.2.2.1 hret.2.1.2.2
  have hwait : (((protocol q).step ring C root) root).mode =
      .RWAIT := ha.2.2.2.1
  rw [hmode] at hwait
  cases hwait

/-- Case E: for every allowed root-outgoing service, whether the
physical phase is OUTWARD or RETURN, the phase is preserved.
The RETURN(1) case has been shown impossible, not assumed away. -/
theorem resetTrialRootOutgoingPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hp : ResetTrialPhysical ring C root)
    (ha : ResetTrialAllowed ring root C root) :
    ResetTrialPhysical ring ((protocol q).step ring C root) root := by
  rcases hp with hout | hret
  · rcases hout with ⟨j, hj⟩
    by_cases hfirst : j = 1
    · subst j
      exact resetTrialRootOutWaitPreservesPhysical
        ring C root hc (Or.inl ⟨1, hj⟩) hsp ha hj.1
        hj.2.2 (Or.inr hj.2.1.1.2.2)
    · have hbefore : 1 < j := by
        have hpos := hj.2.1.1.1
        omega
      have hclear := hj.2.1.2 1 (by omega) hbefore
      exact resetTrialRootOutWaitPreservesPhysical
        ring C root hc (Or.inl ⟨j, hj⟩) hsp ha hj.1
        hclear.1 (Or.inl hclear.2)
  · rcases hret with ⟨j, hj⟩
    by_cases hfirst : j = 1
    · subst j
      exact False.elim
        (resetTrialRootRlTerminalExcluded
          ring C root hc hsp hj ha)
    · have hne : 1 ≠ j := Ne.symm hfirst
      have hb : 1 ≤ (compileAdvice q).b :=
        Nat.le_trans hj.2.1.1 hj.2.1.2.1
      have hclear := hj.2.2.2 1 (by omega) hb hne
      exact resetTrialRootOutWaitPreservesPhysical
        ring C root hc (Or.inr ⟨j, hj⟩) hsp ha hj.1
        hclear.1 (Or.inl hclear.2)

end Counter
end L3
/-!
Additional spatial HOLD and top-source certificates.
The two extra HOLD classes are needed for an
exhaustive cover: E/RR before a non-top outward front, and RL/E
on an edge whose SOURCE is the returning front.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- If a selected internal pair preserves its own bit/token at
both sites, the rest are framed. No assumption on its modes,
leases, grants or other Cartesian state is needed. -/
theorem resetTrialInternalPairFieldCongr {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C (site ring root k))
    (hx :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root k)).bit =
          (C (site ring root k)).bit ∧
        (D (site ring root k)).tok =
          (C (site ring root k)).tok)
    (hy :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root (k + 1))).bit =
          (C (site ring root (k + 1))).bit ∧
        (D (site ring root (k + 1))).tok =
          (C (site ring root (k + 1))).tok) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  apply resetTrialPhysicalDigitsCongr ring C
    ((protocol q).step ring C (site ring root k))
    root ha.2.2.2 ?_ hp
  intro i hi hib
  by_cases he : i = k
  · subst i
    exact hx
  · by_cases hnext : i = k + 1
    · subst i
      exact hy
    · have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) he
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib hkb hnext
      have hf := step_frame ring C (site ring root k)
        (site ring root i) hnotx hnoty
      constructor
      · exact congrArg
          (fun a : Agent (compileAdvice q) => a.bit) hf
      · exact congrArg
          (fun a : Agent (compileAdvice q) => a.tok) hf

/-- Extra class G: serving the predecessor of an RR at digit
k+1<b leaves the RR in place. This is distinct from the top
turn, and is not an E/E edge. -/
theorem resetTrialOutwardPredecessorHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 < (compileAdvice q).b)
    (hout : ResetOutwardPhysical ring C root (k + 1))
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hleft := hout.2.1.2 k hk (by omega)
  have hrightTok : byy.tok = .RR :=
    hout.2.1.1.2.2
  have hrightBit : byy.bit = false := hout.2.2
  have hrow := resetTrialBankPredecessorHoldsSymbolic
    bx byy (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < (compileAdvice q).b; omega)
    (by rfl)
    (by change k + 1 < (compileAdvice q).b; exact hkb)
    (by change (C (site ring root k)).tok = .E; exact hleft.2)
    hrightTok
    (by change (C (site ring root k)).bit = false; exact hleft.1)
    hrightBit
  have hpairs := resetTrialSelectedRowFields ring C root hc
    (Or.inl ⟨k + 1, hout⟩) hsp k (by omega)
    .E .RR false false hrow
  have hx :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root k)).bit =
          (C (site ring root k)).bit ∧
        (D (site ring root k)).tok =
          (C (site ring root k)).tok :=
    ⟨hpairs.1.trans hleft.1.symm,
      hpairs.2.1.trans hleft.2.symm⟩
  have hy :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root (k + 1))).bit =
          (C (site ring root (k + 1))).bit ∧
        (D (site ring root (k + 1))).tok =
          (C (site ring root (k + 1))).tok :=
    ⟨hpairs.2.2.1.trans hrightBit.symm,
      hpairs.2.2.2.trans hrightTok.symm⟩
  exact resetTrialInternalPairFieldCongr ring C root hc
    (Or.inl ⟨k + 1, hout⟩) k hk (by omega) ha hx hy

/-- Literal BANK row: a returning RL at the source with a
zero/empty successor does not advance rightward or collide. -/
theorem resetTrialBankReturnSourceHoldSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .RL) (hbx : x.bit = false)
    (hty : y.tok = .E) (hby : y.bit = false) :
    let z := bankPair x y y.role b theta
    z.1.tok = .RL ∧ z.1.bit = false ∧
      z.2.tok = .E ∧ z.2.bit = false := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  have hbpos : b ≠ 0 := by omega
  by_cases htop : x.role + 1 = b
  · simp [bankPair, hxne, hyne, hx, hlt, hxle,
      hy, hyle, hypos, hxb, htx, hbx, hty, hby,
      hnlt, htop, hbpos]
  · simp [bankPair, hxne, hyne, hx, hlt, hxle,
      hy, hyle, hypos, hxb, htx, hbx, hty, hby,
      hnlt, htop, hbpos]

/-- Extra class H: a returning RL as the SOURCE of a forward
edge remains at its current digit, and its next (empty) digit
remains empty. This is a distinct HOLD, not a retreat. -/
theorem resetTrialReturnSourceHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hret : ResetReturnPhysical ring C root k)
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C (site ring root k)) root := by
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hright := hret.2.2.2 (k + 1)
    (by omega) hkb (by omega)
  have hleftTok : bx.tok = .RL := hret.2.1.2.2
  have hleftBit : bx.bit = false := hret.2.2.1
  have hrow := resetTrialBankReturnSourceHoldSymbolic
    bx byy (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < (compileAdvice q).b; omega)
    (by rfl) hleftTok hleftBit
    hright.2
    hright.1
  have hpairs := resetTrialSelectedRowFields ring C root hc
    (Or.inr ⟨k, hret⟩) hsp k (by omega)
    .RL .E false false hrow
  have hx :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root k)).bit =
          (C (site ring root k)).bit ∧
        (D (site ring root k)).tok =
          (C (site ring root k)).tok :=
    ⟨hpairs.1.trans hleftBit.symm,
      hpairs.2.1.trans hleftTok.symm⟩
  have hy :
      let D := (protocol q).step ring C (site ring root k)
      (D (site ring root (k + 1))).bit =
          (C (site ring root (k + 1))).bit ∧
        (D (site ring root (k + 1))).tok =
          (C (site ring root (k + 1))).tok :=
    ⟨hpairs.2.2.1.trans hright.1.symm,
      hpairs.2.2.2.trans hright.2.symm⟩
  exact resetTrialInternalPairFieldCongr ring C root hc
    (Or.inr ⟨k, hret⟩) k hk hkb ha hx hy

end Counter
end L3
/-!
Top active source (site b) and the outside/root seam.
The top source's bit/token are invariant unless it is IR.
For a physical RETURN front or topmost OUTWARD front, IR is absent.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- Literal BANK: an active source at the top role b cannot
execute an internal source row. Its bit and worker are unchanged
unless its worker is the specially erased top IR. -/
theorem resetTrialBankTopSourceNoIR
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = b) (hb : 0 < b)
    (ht : x.tok ≠ .IR) :
    let z := bankPair x y (packNext x.role y.role b) b theta
    z.1.bit = x.bit ∧ z.1.tok = x.tok := by
  have hxne : x.role ≠ 0 := by omega
  have hxnlt : ¬ x.role < b := by omega
  have hxguard : ¬ (1 ≤ x.role ∧ x.role < b) := by omega
  have hb0 : b ≠ 0 := by omega
  by_cases hchanged : packNext b y.role b = y.role
  · simp [bankPair, hx, hb, hb0, ht, hxne, hxnlt,
      hxguard, hchanged] <;>
      repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)
  · simp [bankPair, hx, hb, hb0, ht, hxne, hxnlt,
      hxguard, hchanged] <;>
      repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)

/-- The successor of the top digit cannot coincide with any
positive active digit. If it enters the root, that is harmless
for digit bits/workers and handled by next-cut root waiting. -/
theorem resetTrialTopResponderNotActive {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (i : Nat) (hi : 1 ≤ i)
    (hib : i ≤ (compileAdvice q).b) :
    site ring root i ≠
      ring.rightNeighbor (site ring root (compileAdvice q).b) := by
  intro heq
  have hbefore : i - 1 + 1 = i := by omega
  have hsource :
      ring.rightNeighbor (site ring root (i - 1)) =
      ring.rightNeighbor
        (site ring root (compileAdvice q).b) := by
    calc
      ring.rightNeighbor (site ring root (i - 1)) =
          site ring root (i - 1 + 1) := rfl
      _ = site ring root i := by rw [hbefore]
      _ = ring.rightNeighbor
          (site ring root (compileAdvice q).b) := heq
  have he := resetTrialNeighborInjective ring hsource
  have hdiff := resetCompleteSitesDifferent ring C root hc
    (i - 1) (compileAdvice q).b
    (by omega) (by omega) (by omega)
  exact hdiff he

/-- Actual Protocol.step at the top source, with a non-IR worker,
preserves all active digit bit/token fields. The responder may be
an exterior site, or the root in a ring of exactly b+1 sites. -/
theorem resetTrialTopSourcePreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b))
    (hnoIR : (C (site ring root (compileAdvice q).b)).tok ≠ .IR) :
    ResetTrialPhysical ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root := by
  let b := (compileAdvice q).b
  let e := site ring root b
  let y := ring.rightNeighbor e
  let bx := bankCell (C e) (C e).pack.val
  let byy := bankCell (C y) (C y).pack.val
  let z := bankPair bx byy (packNext bx.role byy.role b)
    b (compileAdvice q).theta
  let D := (protocol q).step ring C e
  have hb : 0 < b := by
    have hh := resetTrialCompiledWidth q
    dsimp [b]
    omega
  have hrole : bx.role = b := hc b (by omega)
  have hbank : z.1.bit = bx.bit ∧ z.1.tok = bx.tok :=
    resetTrialBankTopSourceNoIR bx byy b
      (compileAdvice q).theta hrole hb hnoIR
  have hproj :
      resetAgentBankTrip (D e) = resetCellBankTrip z.1 :=
    (resetTrialSelectedBankTrip ring C root e hc hp hsp).1
  have hpairs := resetTrialTripBitTok (D e) z.1 hproj
  have hsource :
      (D e).bit = (C e).bit ∧
        (D e).tok = (C e).tok :=
    ⟨hpairs.1.trans hbank.1, hpairs.2.trans hbank.2⟩
  apply resetTrialPhysicalDigitsCongr ring C D root
    ha.2.2.2 ?_ hp
  intro i hi hib
  by_cases htop : i = b
  · subst i
    exact hsource
  · have hnotx : site ring root i ≠ e :=
      resetCompleteSitesDifferent ring C root hc i b
        hib (by omega) htop
    have hnoty : site ring root i ≠ y :=
      resetTrialTopResponderNotActive ring C root hc i hi hib
    have hframe := step_frame ring C e (site ring root i)
      hnotx hnoty
    constructor
    · exact congrArg
        (fun a : Agent (compileAdvice q) => a.bit) hframe
    · exact congrArg
        (fun a : Agent (compileAdvice q) => a.tok) hframe

/-- The topmost genuine OUTWARD RR is not an IR, and hence a
top-source service leaves the front in place. -/
theorem resetTrialTopOutwardHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hout : ResetOutwardPhysical ring C root
      (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root := by
  have ht : (C (site ring root (compileAdvice q).b)).tok =
      .RR := hout.2.1.1.2.2
  apply resetTrialTopSourcePreservesPhysical ring C root hc
    (Or.inl ⟨(compileAdvice q).b, hout⟩) hsp ha
  intro hbad
  rw [ht] at hbad
  cases hbad

/-- All RETURN phases, including a hypothetical RL at digit b,
have a non-IR worker at the top. The top-source edge preserves
the phase, whether or not its responder is the root. -/
theorem resetTrialTopReturnHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat)
    (hret : ResetReturnPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b)) :
    ResetTrialPhysical ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root := by
  have hnotIR :
      (C (site ring root (compileAdvice q).b)).tok ≠ .IR := by
    by_cases hj : j = (compileAdvice q).b
    · have ht : (C (site ring root (compileAdvice q).b)).tok =
          .RL := by
        rw [← hj]
        exact hret.2.1.2.2
      intro hbad
      rw [ht] at hbad
      cases hbad
    · have hb : 1 ≤ (compileAdvice q).b :=
        Nat.le_trans hret.2.1.1 hret.2.1.2.1
      have hc := hret.2.2.2 (compileAdvice q).b
        hb (by omega) (Ne.symm hj)
      intro hbad
      rw [hc.2] at hbad
      cases hbad
  exact resetTrialTopSourcePreservesPhysical ring C root hc
    (Or.inr ⟨j, hret⟩) hsp ha hnotIR

end Counter
end L3
/-!
Exhaustive spatial positional cover and unconditional
trial closure.
The proof covers both spatial and SMALL compiled branches; it
does not appeal to a reachable-state ghost or an unstated invariant.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- No selected source within the complete active interval:
either the selected edge enters the root from outside, or both
endpoints lie fully outside all active sites. -/
theorem resetTrialNoActiveSourcePreservesPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (ha : ResetTrialAllowed ring root C e)
    (hno : ∀ k : Nat, k ≤ (compileAdvice q).b →
      e ≠ site ring root k) :
    ResetTrialPhysical ring ((protocol q).step ring C e) root := by
  by_cases hroot : ring.rightNeighbor e = root
  · have hex : ∀ i : Nat, 1 ≤ i →
        i ≤ (compileAdvice q).b → e ≠ site ring root i := by
      intro i _ hib
      exact hno i hib
    exact resetTrialIncomingRootExterior ring C root e
      hc hp ha hroot hex
  · rcases resetTrialEdgeGeometry (q := q) ring root e with
      hsource | hincoming | houtside
    · obtain ⟨k, hk, he⟩ := hsource
      exact False.elim ((hno k hk) he)
    · exact False.elim (hroot hincoming)
    · exact resetTrialOutsidePreservesPhysical
        ring C root e houtside hp

/-- The outward case covers EVERY selected edge. In addition to
the front-movement cases it includes the two possible HOLDS at
the left side of the front and the top-source edge. -/
theorem resetTrialOutwardAllEdges {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hout : ResetOutwardPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e) :
    ResetTrialPhysical ring ((protocol q).step ring C e) root := by
  have hp : ResetTrialPhysical ring C root :=
    Or.inl ⟨j, hout⟩
  by_cases hsource : ∃ k : Nat,
      k ≤ (compileAdvice q).b ∧ e = site ring root k
  · obtain ⟨k, hkb, he⟩ := hsource
    subst e
    by_cases hzero : k = 0
    · subst k
      change ResetTrialPhysical ring
        ((protocol q).step ring C root) root
      exact resetTrialRootOutgoingPhysical
        ring C root hc hsp hp ha
    · have hkpos : 1 ≤ k := by omega
      by_cases htop : k = (compileAdvice q).b
      · subst k
        by_cases hjtop : j = (compileAdvice q).b
        · subst j
          exact resetTrialTopOutwardHold
            ring C root hc hsp hout ha
        · have hjlt : j < (compileAdvice q).b := by
            have hjbound := hout.2.1.1.2.1
            omega
          exact resetTrialAheadPreservesPhysical
            ring C root hc j (compileAdvice q).b
            hout ha hjlt (by omega)
      · have hklt : k < (compileAdvice q).b := by omega
        by_cases hfar : k + 1 < j
        · have hx := hout.2.1.2 k hkpos (by omega)
          have hy := hout.2.1.2 (k + 1) (by omega) hfar
          exact resetTrialEmptyInternalPreservesPhysical
            ring C root hc hsp hp k hkpos (by omega)
            hx hy ha
        · by_cases hprev : k + 1 = j
          · by_cases hjtop : j = (compileAdvice q).b
            · subst j
              have hkminus : k = (compileAdvice q).b - 1 := by
                omega
              subst k
              exact resetTrialOutwardTopTurn
                ring C root hc hsp hout ha
            · have hnext : ResetOutwardPhysical ring C root
                  (k + 1) := by
                rw [hprev]
                exact hout
              exact resetTrialOutwardPredecessorHold
                ring C root hc hsp k hkpos (by omega)
                hnext ha
          · by_cases hfront : k = j
            · subst k
              exact resetTrialOutwardAdvance
                ring C root hc hsp j hout ha hklt
            · have hahead : j < k := by omega
              exact resetTrialAheadPreservesPhysical
                ring C root hc j k hout ha hahead hkb
  · have hno : ∀ k : Nat,
        k ≤ (compileAdvice q).b →
        e ≠ site ring root k := by
      intro k hk he
      exact hsource ⟨k, hk, he⟩
    exact resetTrialNoActiveSourcePreservesPhysical
      ring C root e hc hp ha hno

/-- The return case covers EVERY edge. The real retreat is the
edge entering the RL from the left; the edge leaving RL to the
right is a HOLD, not a retreat. The top-source special row and
the terminal root RL exclusion are handled separately. -/
theorem resetTrialReturnAllEdges {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hret : ResetReturnPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e) :
    ResetTrialPhysical ring ((protocol q).step ring C e) root := by
  have hp : ResetTrialPhysical ring C root :=
    Or.inr ⟨j, hret⟩
  by_cases hsource : ∃ k : Nat,
      k ≤ (compileAdvice q).b ∧ e = site ring root k
  · obtain ⟨k, hkb, he⟩ := hsource
    subst e
    by_cases hzero : k = 0
    · subst k
      change ResetTrialPhysical ring
        ((protocol q).step ring C root) root
      exact resetTrialRootOutgoingPhysical
        ring C root hc hsp hp ha
    · have hkpos : 1 ≤ k := by omega
      by_cases htop : k = (compileAdvice q).b
      · subst k
        exact resetTrialTopReturnHold
          ring C root hc hsp j hret ha
      · have hklt : k < (compileAdvice q).b := by omega
        by_cases hprev : k + 1 = j
        · have hnext : ResetReturnPhysical ring C root (k + 1) := by
            rw [hprev]
            exact hret
          exact resetTrialReturnRetreat
            ring C root hc hsp k hkpos (by omega) hnext ha
        · by_cases hfront : k = j
          · subst k
            exact resetTrialReturnSourceHold
              ring C root hc hsp j (by omega)
              (by omega) hret ha
          · have hx : (C (site ring root k)).bit = false ∧
                (C (site ring root k)).tok = .E :=
              hret.2.2.2 k hkpos (by omega) hfront
            have hy : (C (site ring root (k + 1))).bit = false ∧
                (C (site ring root (k + 1))).tok = .E :=
              hret.2.2.2 (k + 1) (by omega)
                (by omega) hprev
            exact resetTrialEmptyInternalPreservesPhysical
              ring C root hc hsp hp k hkpos (by omega)
              hx hy ha
  · have hno : ∀ k : Nat,
        k ≤ (compileAdvice q).b →
        e ≠ site ring root k := by
      intro k hk he
      exact hsource ⟨k, hk, he⟩
    exact resetTrialNoActiveSourcePreservesPhysical
      ring C root e hc hp ha hno

/-- The real BANK physical one-step invariant for every compiled
protocol, all complete configurations and every allowed edge.
No historical ghost marker or reachability qualifier is needed. -/
theorem resetPhysicalRowClosure {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetPhysicalRowClosure (q := q) ring root := by
  intro C e hc hp ha
  cases hs : (compileAdvice q).useSmall with
  | true =>
      exact resetTrialSmallPhysicalClosure ring root hs
        C e hc hp ha
  | false =>
      rcases hp with hout | hret
      · obtain ⟨j, hj⟩ := hout
        exact resetTrialOutwardAllEdges
          ring C root hc hs j hj e ha
      · obtain ⟨j, hj⟩ := hret
        exact resetTrialReturnAllEdges
          ring C root hc hs j hj e ha

/-- Run-level physical invariant, now without the formerly open
row-closure hypothesis. It starts from the genuine launch and
stops on exactly the per-step conditions of ResetTrialWord. -/
theorem resetTrialPhaseRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (Czero : Config q n)
    (hlaunch : ResetLaunchPhysical ring Czero root)
    (w : List (Fin n))
    (hw : ResetTrialWord ring root Czero w) :
    ResetTrialPhysical ring (Word ring w Czero) root := by
  exact resetTrialPhaseConditional ring root
    (resetPhysicalRowClosure (q := q) ring root)
    Czero w hlaunch.1
    (resetTrialStartOutward ring Czero root hlaunch) hw

/-- Appendix C part (c) for a completed RESET return along a
role-stable, root-grant-free, no-timeout trial, with no extra
ghost/row-closure premise. -/
theorem resetTrialPartC {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (Czero : Config q n)
    (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlaunch : ResetLaunchPhysical ring Czero root)
    (w : List (Fin n))
    (hw : ResetTrialWord ring root Czero w)
    (htok : ((Word ring w Czero)
      (site ring root 1)).tok = .RL) :
    ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (((protocol q).step ring (Word ring w Czero) root)
        (site ring root j)).bit = false ∧
      (((protocol q).step ring (Word ring w Czero) root)
        (site ring root j)).tok = .E := by
  exact resetTrialPartCConditional ring root Czero
    hn hsp hlaunch (resetPhysicalRowClosure (q := q) ring root)
    w hw htok

end Counter
end L3
/-!
First OPEN clock ingredient of Appendix C, Lemma bank.

This is the finite deterministic reset-front *clock* and its exact
uniform-edge expectation. The clock abstracts the genuinely launched
front, with the terminal root service as the final nominated hit.
It does not silently identify a physical BANK configuration with
this abstract chain. In particular, the actual stopped coupling at
role defect, grant, and root timeout is still OPEN.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open Classical

/-- Abstract front stage of one launched reset episode. -/
inductive ResetClockStage where
  | outward (j : Nat)
  | returning (j : Nat)
  | finished
  deriving DecidableEq, Repr

/-- The only active stage indices correspond to physical digits. -/
def resetClockValid (b : Nat) : ResetClockStage → Prop
  | .outward j => 1 ≤ j ∧ j ≤ b
  | .returning j => 1 ≤ j ∧ j ≤ b
  | .finished => True

/-- Invalid scratch stage labels and finished are absorbing targets.
Every physically authenticated preterminal stage is valid. -/
def resetClockTerminal (b : Nat) (s : ResetClockStage) : Prop :=
  s = .finished ∨ ¬ resetClockValid b s

/-- Classical decidability for the terminal test, so every `if` on it
uses one instance. -/
noncomputable instance resetClockTerminalDecidable (b : Nat)
    (s : ResetClockStage) : Decidable (resetClockTerminal b s) :=
  Classical.propDecidable _

/-- Remaining productive services after the current front cut.
OUTWARD(j) has b-j advances, one top turn, j-independent
b-2 retreats, and one root return: total 2b-j.
RETURN(j) has j-1 retreats and one root return: total j. -/
def resetClockRank (b : Nat) : ResetClockStage → Nat
  | .outward j => 2 * b - j
  | .returning j => j
  | .finished => 0

/-- Unique edge prescribed for the next productive hit.
OUTWARD(b) nominates the preceding top-turn edge, not site b.
RETURN(1) nominates the root outgoing edge as its terminal hit. -/
def resetClockNominated {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (b : Nat) :
    ResetClockStage → Fin n
  | .outward j =>
      if j < b then site ring root j else site ring root (b - 1)
  | .returning j =>
      if 1 < j then site ring root (j - 1) else root
  | .finished => root

/-- One nominated reset-front hit, independently of the arrival
clock. Every other edge is idle for the abstract front stage. -/
def resetClockAdvance (b : Nat) : ResetClockStage → ResetClockStage
  | .outward j =>
      if j < b then .outward (j + 1) else .returning (b - 1)
  | .returning j =>
      if 1 < j then .returning (j - 1) else .finished
  | .finished => .finished

/-- Absorbing finite-IID abstract reset-front transition.
This is NOT the full physical Protocol.step. -/
noncomputable def resetClockNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (s : ResetClockStage) (e : Fin n) : ResetClockStage :=
  if resetClockTerminal b s then s
  else if e = resetClockNominated ring root b s then
    resetClockAdvance b s
  else s

/-- Every valid, unfinished stage loses exactly one productive
service when its nominated edge is selected. -/
theorem resetClockAdvanceRank (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage)
    (hv : resetClockValid b s)
    (hnot : s ≠ .finished) :
    resetClockRank b (resetClockAdvance b s) + 1 =
      resetClockRank b s := by
  cases s with
  | finished =>
      exact False.elim (hnot rfl)
  | outward j =>
      change 1 ≤ j ∧ j ≤ b at hv
      by_cases hj : j < b
      · simp [resetClockAdvance, resetClockRank, hj]
        omega
      · have heq : j = b := by omega
        simp [resetClockAdvance, resetClockRank, hj]
        omega
  | returning j =>
      change 1 ≤ j ∧ j ≤ b at hv
      by_cases hj : 1 < j
      · simp [resetClockAdvance, resetClockRank, hj]
        omega
      · have heq : j = 1 := by omega
        simp [resetClockAdvance, resetClockRank, hj]
        omega

/-- A nontarget abstract stage is both valid and unfinished. -/
theorem resetClockNotTerminal (b : Nat) (s : ResetClockStage)
    (h : ¬ resetClockTerminal b s) :
    resetClockValid b s ∧ s ≠ .finished := by
  constructor
  · by_cases hv : resetClockValid b s
    · exact hv
    · exact False.elim (h (Or.inr hv))
  · intro he
    exact h (Or.inl he)

/-- Exactly one progress unit is charged on a nominated hit,
and zero otherwise, including after an absorbing terminal cut. -/
theorem resetClockStepBalance {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage) (e : Fin n) :
    resetClockRank b (resetClockNext ring root b s e) +
      (if ¬ resetClockTerminal b s ∧
          e = resetClockNominated ring root b s then 1 else 0) =
      resetClockRank b s := by
  classical
  by_cases ht : resetClockTerminal b s
  · have hh :
        ¬ (¬ resetClockTerminal b s ∧
          e = resetClockNominated ring root b s) := by
      intro hh
      exact hh.1 ht
    simp [resetClockNext, ht, hh]
  · by_cases he : e = resetClockNominated ring root b s
    · have hh :
          ¬ resetClockTerminal b s ∧
            e = resetClockNominated ring root b s :=
        ⟨ht, he⟩
      have hv := resetClockNotTerminal b s ht
      have hd := resetClockAdvanceRank b hb s hv.1 hv.2
      simpa only [resetClockNext, if_neg ht, if_pos he,
        if_pos hh] using hd
    · have hh :
          ¬ (¬ resetClockTerminal b s ∧
            e = resetClockNominated ring root b s) := by
        intro h
        exact he h.2
      simp [resetClockNext, ht, he, hh]

/-- A finite edge word acts on the abstract front. -/
noncomputable def resetClockAfter {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (b : Nat) :
    ResetClockStage → List (Fin n) → ResetClockStage
  | s, [] => s
  | s, e :: w =>
      resetClockAfter ring root b (resetClockNext ring root b s e) w

/-- Predictable productive-hit count, not a retrospective tally of
only eventually completed resets. It is bounded even on failures. -/
noncomputable def resetClockHits {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (b : Nat) :
    ResetClockStage → List (Fin n) → Nat
  | _, [] => 0
  | s, e :: w =>
      (if ¬ resetClockTerminal b s ∧
          e = resetClockNominated ring root b s then 1 else 0) +
        resetClockHits ring root b
          (resetClockNext ring root b s e) w

/-- Exact finite-word progress accounting:
remaining productive work plus hits equals the original work. -/
theorem resetClockHitsConserved {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage) (w : List (Fin n)) :
    resetClockRank b (resetClockAfter ring root b s w) +
      resetClockHits ring root b s w = resetClockRank b s := by
  induction w generalizing s with
  | nil =>
      simp [resetClockAfter, resetClockHits]
  | cons e es ih =>
      have hstep := resetClockStepBalance ring root b hb s e
      have htail := ih (resetClockNext ring root b s e)
      change
        resetClockRank b
            (resetClockAfter ring root b
              (resetClockNext ring root b s e) es) +
          ((if ¬ resetClockTerminal b s ∧
              e = resetClockNominated ring root b s then 1 else 0) +
            resetClockHits ring root b
              (resetClockNext ring root b s e) es) =
          resetClockRank b s
      omega

/-- From the genuinely launched OUTWARD(1), no word can contain
more than 2b-1 further productive services. -/
theorem resetClockPostLaunchCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b) (w : List (Fin n)) :
    resetClockHits ring root b (.outward 1) w ≤ 2 * b - 1 := by
  have hh := resetClockHitsConserved
    ring root b hb (.outward 1) w
  change
    resetClockRank b
        (resetClockAfter ring root b (.outward 1) w) +
      resetClockHits ring root b (.outward 1) w =
      2 * b - 1 at hh
  omega

/-- Including the launch, the budget 2b+2 is conservative. -/
theorem resetClockProductiveBudget {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b) (w : List (Fin n)) :
    1 + resetClockHits ring root b (.outward 1) w ≤
      2 * b + 2 := by
  have hh := resetClockPostLaunchCount ring root b hb w
  omega

/-- On a completed abstract reset, exactly 2b productive services
were accepted, including launch and the final root RL consumption.
This is the sharper combinatorial certificate behind L=2b+2. -/
theorem resetClockCompletedCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b) (w : List (Fin n))
    (hfinished :
      resetClockRank b
        (resetClockAfter ring root b (.outward 1) w) = 0) :
    1 + resetClockHits ring root b (.outward 1) w =
      2 * b := by
  have hh := resetClockHitsConserved ring root b hb
    (.outward 1) w
  change
    resetClockRank b
        (resetClockAfter ring root b (.outward 1) w) +
      resetClockHits ring root b (.outward 1) w =
      2 * b - 1 at hh
  rw [hfinished] at hh
  omega

/-- The selected rate-1/n edge decrements the rank. -/
theorem resetClockNominatedDrop {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage)
    (h : ¬ resetClockTerminal b s) :
    resetClockRank b
        (resetClockNext ring root b s
          (resetClockNominated ring root b s)) + 1 ≤
      resetClockRank b s := by
  have hv := resetClockNotTerminal b s h
  have hh := resetClockAdvanceRank b hb s hv.1 hv.2
  simp only [resetClockNext, if_neg h, ↓reduceIte]
  omega

/-- Every non-nominated edge leaves the rank unchanged. -/
theorem resetClockAllEdgesWeak {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage)
    (h : ¬ resetClockTerminal b s) (e : Fin n) :
    resetClockRank b (resetClockNext ring root b s e) ≤
      resetClockRank b s := by
  by_cases he : e = resetClockNominated ring root b s
  · subst e
    have hh := resetClockNominatedDrop ring root b hb s h
    omega
  · simp [resetClockNext, h, he]

/-- The genuine uniform-IID edge-clock API bounds all finite-horizon
expected costs by n times the outstanding productive services.
The proof uses the existing nominated-edge Bellman theorem. -/
theorem resetClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b)
    (s : ResetClockStage) (T : Nat) :
    costNumerator (resetClockNext ring root b)
      (resetClockTerminal b) s T ≤
      n ^ T * (n * resetClockRank b s) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (resetClockNext ring root b)
    (resetClockTerminal b)
    (resetClockRank b)
    (resetClockNominated ring root b)
    (fun x hx => resetClockNominatedDrop ring root b hb x hx)
    (fun x hx e => resetClockAllEdgesWeak ring root b hb x hx e)
    s T

/-- The independent nominated edge clock gives mean at most
n(2b-1) from a postlaunch front in the abstract process. -/
theorem resetClockExpected {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 0 < n) (b : Nat) (hb : 2 ≤ b) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockNext ring root b)
      (resetClockTerminal b) (.outward 1)
      ((n * (2 * b - 1) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (resetClockNext ring root b) (resetClockTerminal b)
    hn (.outward 1) (n * (2 * b - 1))).2
  intro T
  simpa only [resetClockRank] using
    (resetClockCost ring root b hb (.outward 1) T)

/-- Physical interpretation of an abstract preterminal stage.
The final absorbing stage requires a separate genuine root return. -/
def resetClockStageAt {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : ResetClockStage → Prop
  | .outward j => ResetOutwardPhysical ring C root j
  | .returning j => ResetReturnPhysical ring C root j
  | .finished => False

/-- A genuine real Protocol RESET launch initializes the abstract
clock at OUTWARD(1) without any assumption on suffix scratch. -/
theorem resetClockLaunchStage {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (h : ResetLaunchPhysical ring C root) :
    resetClockStageAt ring C root (.outward 1) := by
  rcases h with ⟨_, _, hb, hw, hbit, htok, _⟩
  change ResetOutwardPhysical ring C root 1
  refine ⟨hw, ?_, hbit⟩
  refine ⟨⟨by omega, hb, htok⟩, ?_⟩
  intro i hi hlt
  omega

end Counter
end L3
/-!
Uniqueness of the phase visible in an authenticated
preterminal physical snapshot. This supplies a *state-only* stage
label for the later physical/abstract clock coupling.
-/

namespace L3
namespace Counter

set_option autoImplicit false

/-- Two simultaneously claimed returning fronts have the same digit
because each returning snapshot clears all other active workers. -/
theorem resetClockReturnUnique {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j k : Nat)
    (hj : ResetReturnPhysical ring C root j)
    (hk : ResetReturnPhysical ring C root k) : j = k := by
  by_cases he : j = k
  · exact he
  · have hbit : 1 ≤ j := hj.2.1.1
    have hbound : j ≤ (compileAdvice q).b := hj.2.1.2.1
    have hE := (hk.2.2.2 j hbit hbound he).2
    have hRL : (C (site ring root j)).tok = .RL :=
      hj.2.1.2.2
    rw [hRL] at hE
    cases hE

/-- An OUTWARD snapshot and a RETURN snapshot cannot coexist.
A returning phase leaves only its own RL worker occupied. -/
theorem resetClockMixedImpossible {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j k : Nat)
    (hout : ResetOutwardPhysical ring C root j)
    (hret : ResetReturnPhysical ring C root k) : False := by
  by_cases he : j = k
  · have hRR : (C (site ring root j)).tok = .RR :=
      hout.2.1.1.2.2
    have hRL : (C (site ring root k)).tok = .RL :=
      hret.2.1.2.2
    rw [he, hRL] at hRR
    cases hRR
  · have hjpos : 1 ≤ j := hout.2.1.1.1
    have hjbound : j ≤ (compileAdvice q).b :=
      hout.2.1.1.2.1
    have hE := (hret.2.2.2 j hjpos hjbound he).2
    have hRR : (C (site ring root j)).tok = .RR :=
      hout.2.1.1.2.2
    rw [hRR] at hE
    cases hE

/-- Any physically authenticated preterminal phase admits a
corresponding (abstract) stage witness. -/
theorem resetClockStageExists {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hp : ResetTrialPhysical ring C root) :
    ∃ s : ResetClockStage, resetClockStageAt ring C root s := by
  rcases hp with hout | hret
  · obtain ⟨j, hj⟩ := hout
    exact ⟨.outward j, hj⟩
  · obtain ⟨j, hj⟩ := hret
    exact ⟨.returning j, hj⟩

/-- The physical stage witness is unique; this is a consequence
of literal bit/token contents, with no ghost generation stamps. -/
theorem resetClockStageUnique {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s t : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ht : resetClockStageAt ring C root t) :
    s = t := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      cases t with
      | finished =>
          cases ht
      | outward k =>
          have he : j = k :=
            resetOutwardPhysicalUnique ring C root j k hs ht
          exact congrArg ResetClockStage.outward he
      | returning k =>
          exact False.elim
            (resetClockMixedImpossible ring C root j k hs ht)
  | returning j =>
      cases t with
      | finished =>
          cases ht
      | outward k =>
          exact False.elim
            (resetClockMixedImpossible ring C root k j ht hs)
      | returning k =>
          have he : j = k :=
            resetClockReturnUnique ring C root j k hs ht
          exact congrArg ResetClockStage.returning he

end Counter
end L3
/-!
Literal arithmetic from the first two parameter displays
of Lemma bank. These certificates alone do not establish the
probabilistic cold-start or regenerative-trial estimates.
-/

namespace L3
namespace Counter

open Classical

set_option autoImplicit false

/-- C.3's cold-start coefficient, not its stochastic conclusion. -/
theorem resetBankColdCoefficient (b : Nat) :
    2 * (13 * (b + 2)) + 5 * b + 13 = 31 * b + 65 ∧
      31 * b + 65 <
        16 * (13 * (b + 2) + b + 2) := by
  constructor <;> omega

/-- The stated successful-trial coefficient is below the
larger alpha_tr coefficient for every threshold K. -/
theorem resetBankTrialCoefficient (b K : Nat) :
    (8 * b + 12) * (K + 1) <
      (32 * (b + 1)) * (K + 1) := by
  have hbase : 8 * b + 12 < 32 * (b + 1) := by omega
  exact Nat.mul_lt_mul_of_pos_right hbase (by omega)

/-- The abstract productive count is below the paper's L=2b+2
with two spare services. This is NOT a watchdog probability. -/
theorem resetBankProductiveCoefficient (b : Nat) :
    2 * b ≤ 2 * b + 2 := by
  omega

end Counter
end L3

/-!
The next three productive-edge proofs duplicate the earlier
BANK-row derivations, but expose their stronger positional results.
The complete all-edge identity simulation remains an explicit premise
in the conditional stopping-cost transfer, NOT an unproved theorem.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

/-- A physical trial stage has a digit index in the legal range. -/
theorem resetClockStageAtValid {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s) :
    resetClockValid (compileAdvice q).b s := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      exact ⟨hs.2.1.1.1, hs.2.1.1.2.1⟩
  | returning j =>
      exact ⟨hs.2.1.1, hs.2.1.2.1⟩

/-- In particular no genuine preterminal physical stage is an
abstract stopping target. -/
theorem resetClockStageAtNotTerminal {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s) :
    ¬ resetClockTerminal (compileAdvice q).b s := by
  have hv := resetClockStageAtValid ring C root s hs
  intro ht
  rcases ht with hfinished | hinvalid
  · cases s with
    | finished =>
        cases hs
    | outward j =>
        cases hfinished
    | returning j =>
        cases hfinished
  · exact hinvalid hv

/-- The canonical stage map is defined only at an authenticated
preterminal physical cut, not at arbitrary Cartesian scratch. -/
noncomputable def resetClockPhysicalStage {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hp : ResetTrialPhysical ring C root) :
    ResetClockStage :=
  Classical.choose (resetClockStageExists ring C root hp)

theorem resetClockPhysicalStageSpec {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hp : ResetTrialPhysical ring C root) :
    resetClockStageAt ring C root
      (resetClockPhysicalStage ring C root hp) := by
  exact Classical.choose_spec (resetClockStageExists ring C root hp)

/-- Canonicality is independent of the physical-stage witness. -/
theorem resetClockPhysicalStageEq {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hp : ResetTrialPhysical ring C root)
    (s : ResetClockStage) (hs : resetClockStageAt ring C root s) :
    resetClockPhysicalStage ring C root hp = s := by
  exact resetClockStageUnique ring C root
    (resetClockPhysicalStage ring C root hp) s
    (resetClockPhysicalStageSpec ring C root hp) hs

/-- Bit/token congruence at every digit and a waiting root preserve
a PARTICULAR stage witness, not merely the stage disjunction. -/
theorem resetClockStageAtDigitsCongr {n q : Nat}
    (ring : DirectedRing n) (C D : Config q n)
    (root : Fin n)
    (hw : ResetRootWaiting D root)
    (hfields : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit = (C (site ring root i)).bit ∧
      (D (site ring root i)).tok = (C (site ring root i)).tok)
    (s : ResetClockStage) (hs : resetClockStageAt ring C root s) :
    resetClockStageAt ring D root s := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      change ResetOutwardPhysical ring C root j at hs
      change ResetOutwardPhysical ring D root j
      rcases hs with ⟨_, ⟨⟨hjpos, hjbound, htok⟩, hprefix⟩, hbit⟩
      refine ⟨hw, ?_, ?_⟩
      · refine ⟨⟨hjpos, hjbound, ?_⟩, ?_⟩
        · rw [(hfields j hjpos hjbound).2]
          exact htok
        · intro i hi hij
          have hib : i ≤ (compileAdvice q).b := by omega
          have hf := hfields i hi hib
          constructor
          · rw [hf.1]
            exact (hprefix i hi hij).1
          · rw [hf.2]
            exact (hprefix i hi hij).2
      · rw [(hfields j hjpos hjbound).1]
        exact hbit
  | returning j =>
      change ResetReturnPhysical ring C root j at hs
      change ResetReturnPhysical ring D root j
      rcases hs with ⟨_, ⟨hjpos, hjbound, htok⟩, hbit, hclear⟩
      refine ⟨hw, ⟨hjpos, hjbound, ?_⟩, ?_, ?_⟩
      · rw [(hfields j hjpos hjbound).2]
        exact htok
      · rw [(hfields j hjpos hjbound).1]
        exact hbit
      · intro i hi hib hneq
        have hf := hfields i hi hib
        constructor
        · rw [hf.1]
          exact (hclear i hi hib hneq).1
        · rw [hf.2]
          exact (hclear i hi hib hneq).2

/-- The source existing advance proof already constructs the
specific OUTWARD(j+1) witness. Expose that stronger statement. -/
theorem resetClockPhysicalOutwardAdvance {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hout : ResetOutwardPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C (site ring root j))
    (hj : j < (compileAdvice q).b) :
    ResetOutwardPhysical ring
      ((protocol q).step ring C (site ring root j)) root (j + 1) := by
  let bx := bankCell (C (site ring root j)) j
  let byy := bankCell (C (site ring root (j + 1))) (j + 1)
  have hjpos : 1 ≤ j := hout.2.1.1.1
  have hxpos : 1 ≤ bx.role := by
    change 1 ≤ j
    exact hjpos
  have hxlt : bx.role < (compileAdvice q).b := by
    change j < (compileAdvice q).b
    exact hj
  have hy : byy.role = bx.role + 1 := rfl
  have htok : bx.tok = .RR := by
    change (C (site ring root j)).tok = .RR
    exact hout.2.1.1.2.2
  have hbit : bx.bit = false := by
    change (C (site ring root j)).bit = false
    exact hout.2.2
  have howner := resetTrialBankForwardSymbolic bx byy
    (compileAdvice q).b (compileAdvice q).theta
    hxpos hxlt hy htok hbit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inl ⟨j, hout⟩) hsp j hj .E .RR false false howner
  refine ⟨ha.2.2.2, ?_, hpair.2.2.1⟩
  · refine ⟨⟨by omega, by omega, hpair.2.2.2⟩, ?_⟩
    intro i hi hij
    by_cases he : i = j
    · subst i
      exact ⟨hpair.1, hpair.2.1⟩
    · have hbefore : i < j := by omega
      have hnotx : site ring root i ≠ site ring root j :=
        resetCompleteSitesDifferent ring C root hc i j
          (by omega) (by omega) (by omega)
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root j) := by
        change site ring root i ≠ site ring root (j + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (j + 1) (by omega) (by omega) (by omega)
      have hframe := step_frame ring C
        (site ring root j) (site ring root i) hnotx hnoty
      simpa only [hframe] using hout.2.1.2 i hi hbefore


/-- The case-B proof below exposes RETURN(b-1) after the top turn. -/
theorem resetClockPhysicalOutwardTurn {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hout : ResetOutwardPhysical ring C root (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C
      (site ring root ((compileAdvice q).b - 1))) :
    ResetReturnPhysical ring
      ((protocol q).step ring C
        (site ring root ((compileAdvice q).b - 1))) root
        ((compileAdvice q).b - 1) := by
  let b := (compileAdvice q).b
  let k := b - 1
  have hb : 1 < b := resetTrialCompiledWidth q
  have hkpos : 1 ≤ k := by dsimp [k]; omega
  have hklt : k < b := by dsimp [k]; omega
  have hkadd : k + 1 = b := by dsimp [k]; omega
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hpre := hout.2.1.2 k hkpos (by omega)
  have hsource : bx.tok = .E := by
    change (C (site ring root k)).tok = .E
    exact hpre.2
  have htop : byy.role = b := by
    change k + 1 = b
    exact hkadd
  have htarget : byy.tok = .RR := by
    change (C (site ring root (k + 1))).tok = .RR
    rw [hkadd]
    exact hout.2.1.1.2.2
  have htargetBit : byy.bit = false := by
    change (C (site ring root (k + 1))).bit = false
    rw [hkadd]
    exact hout.2.2
  have howner := resetTrialBankTopTurnSymbolic bx byy
    b (compileAdvice q).theta
    (by change 1 ≤ k; exact hkpos)
    (by change k < b; exact hklt)
    (by rfl) htop hsource htarget htargetBit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inl ⟨b, hout⟩) hsp k hklt .RL .E false false howner
  refine ⟨ha.2.2.2, ?_, hpair.1, ?_⟩
  · exact ⟨hkpos, by omega, hpair.2.1⟩
  · intro i hi hib hneq
    by_cases hitop : i = k + 1
    · subst i
      exact ⟨hpair.2.2.1, hpair.2.2.2⟩
    · have hbefore : i < k := by omega
      have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hneq
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib (by omega) hitop
      have hframe :
          ((protocol q).step ring C
            (site ring root ((compileAdvice q).b - 1)))
            (site ring root i) = C (site ring root i) :=
        step_frame ring C (site ring root k)
          (site ring root i) hnotx hnoty
      rw [hframe]
      exact hout.2.1.2 i hi (by omega)


/-- The case-C proof below exposes RETURN(k) after a retreat. -/
theorem resetClockPhysicalReturnRetreat {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hret : ResetReturnPhysical ring C root (k + 1))
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetReturnPhysical ring
      ((protocol q).step ring C (site ring root k)) root k := by
  let b := (compileAdvice q).b
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hclear := hret.2.2.2 k hk (by omega) (by omega)
  have hsource : bx.tok = .E := by
    change (C (site ring root k)).tok = .E
    exact hclear.2
  have htarget : byy.tok = .RL := by
    change (C (site ring root (k + 1))).tok = .RL
    exact hret.2.1.2.2
  have htargetBit : byy.bit = false := by
    change (C (site ring root (k + 1))).bit = false
    exact hret.2.2.1
  have howner := resetTrialBankRetreatSymbolic bx byy
    b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < b; omega)
    (by rfl) hsource htarget htargetBit
  have hpair := resetTrialSelectedRowFields ring C root hc
    (Or.inr ⟨k + 1, hret⟩) hsp
    k (by omega) .RL .E false false howner
  refine ⟨ha.2.2.2, ?_, hpair.1, ?_⟩
  · exact ⟨hk, by omega, hpair.2.1⟩
  · intro i hi hib hneq
    by_cases hy : i = k + 1
    · subst i
      exact ⟨hpair.2.2.1, hpair.2.2.2⟩
    · have hnotx : site ring root i ≠ site ring root k :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hneq
      have hnoty : site ring root i ≠
          ring.rightNeighbor (site ring root k) := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib hkb hy
      have hframe := step_frame ring C (site ring root k)
        (site ring root i) hnotx hnoty
      simpa only [hframe] using hret.2.2.2 i hi hib hy


/-- The real terminal RWAIT/RL service arms the root. This is
a completion edge, not an edge in ResetTrialAllowed. -/
theorem resetClockPhysicalFinalArms {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : GrantFree C root)
    (hret : ResetReturnPhysical ring C root 1) :
    (((protocol q).step ring C root) root).mode = .ARMED := by
  exact resetTrialRootRlArms ring C root hc
    (Or.inr ⟨1, hret⟩) hsp hret.1 hg
    hret.2.2.1 hret.2.1.2.2

/-- Abstract RETURN(1) nominates the root edge and finishes there. -/
theorem resetClockFinalNominated {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 2 ≤ b) :
    resetClockNext ring root b (.returning 1) root =
      .finished := by
  have hnt : ¬ resetClockTerminal b (.returning 1) := by
    intro ht
    rcases ht with he | hv
    · cases he
    · exact hv ⟨by omega, by omega⟩
  simp [resetClockNext, hnt, resetClockNominated,
    resetClockAdvance]

/-- The remaining missing local assertion, isolated as a
hypothesis rather than introduced as an axiom or claimed theorem.
It includes all allowed phase-preserving services, root services,
the top source, exterior edges, and the three productive rows. -/
noncomputable def ResetClockExactPhysicalSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (C : Config q n) (s : ResetClockStage) (e : Fin n),
    Complete ring C root →
    resetClockStageAt ring C root s →
    ResetTrialAllowed ring root C e →
    resetClockStageAt ring ((protocol q).step ring C e) root
      (resetClockNext ring root (compileAdvice q).b s e)

/-- The actual chain with an absorbing stop bit. It stops on the
first service not in ResetTrialAllowed; at RETURN(1) that includes
the genuine completion service. Stops are absorbing. -/
abbrev ResetClockStoppedState (q n : Nat) := Config q n × Bool

noncomputable def resetClockStoppedNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockStoppedState q n) (e : Fin n) :
    ResetClockStoppedState q n := by
  classical
  exact if x.2 then x
    else if ResetTrialAllowed ring root x.1 e then
      ((protocol q).step ring x.1 e, false)
    else
      ((protocol q).step ring x.1 e, true)

def resetClockStoppedTarget {q n : Nat}
    (x : ResetClockStoppedState q n) : Prop :=
  x.2 = true

/-- A stopped state relates to any ghost clock; an active state
relates only to a matching, complete, physical preterminal stage. -/
def resetClockStoppedRel {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockStoppedState q n) (s : ResetClockStage) : Prop :=
  resetClockStoppedTarget x ∨
    (Complete ring x.1 root ∧ resetClockStageAt ring x.1 root s)

/-- A terminal ghost stage can never be related to a live physical
preterminal snapshot. -/
theorem resetClockStoppedRelTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockStoppedState q n) (s : ResetClockStage)
    (hr : resetClockStoppedRel ring root x s)
    (ht : resetClockTerminal (compileAdvice q).b s) :
    resetClockStoppedTarget x := by
  rcases hr with hx | ⟨_, hs⟩
  · exact hx
  · exact False.elim
      ((resetClockStageAtNotTerminal ring x.1 root s hs) ht)

/-- The conditional physical simulation has the required
edge-by-edge relational successor property. Disallowed edges
immediately set the physical stop bit, with no stage assertion. -/
theorem resetClockStoppedRelStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsim : ResetClockExactPhysicalSimulation (q := q) ring root)
    (x : ResetClockStoppedState q n) (s : ResetClockStage)
    (e : Fin n) (hr : resetClockStoppedRel ring root x s)
    (hq : ¬ resetClockStoppedTarget x)
    (_ht : ¬ resetClockTerminal (compileAdvice q).b s) :
    resetClockStoppedRel ring root (resetClockStoppedNext ring root x e)
      (resetClockNext ring root (compileAdvice q).b s e) := by
  have hx : x.2 = false := by
    cases h : x.2 with
    | false =>
        rfl
    | true =>
        exact False.elim (hq h)
  rcases hr with hstop | ⟨hc, hs⟩
  · exact False.elim (hq hstop)
  · by_cases ha : ResetTrialAllowed ring root x.1 e
    · have heq : resetClockStoppedNext ring root x e =
          ((protocol q).step ring x.1 e, false) := by
        simp [resetClockStoppedNext, hx, ha]
      rw [heq]
      exact Or.inr ⟨resetTrialAllowedComplete ring x.1 root e hc ha,
        hsim x.1 s e hc hs ha⟩
    · have heq : resetClockStoppedNext ring root x e =
          ((protocol q).step ring x.1 e, true) := by
        simp [resetClockStoppedNext, hx, ha]
      rw [heq]
      exact Or.inl rfl

/-- General finite-horizon identity-edge coupling principle.
It allows the physical process to stop EARLIER than the abstract
process and does not assume a.s. finiteness in advance. -/
theorem resetClockCostLeOfStoppedSimulation
    {X A : Type} {n : Nat}
    (nextX : X → Fin n → X) (nextA : A → Fin n → A)
    (Q : X → Prop) (P : A → Prop) (R : X → A → Prop)
    (hstop : ∀ x a, R x a → P a → Q x)
    (hstep : ∀ x a e, R x a → ¬ Q x → ¬ P a →
      R (nextX x e) (nextA a e)) :
    ∀ x a, R x a → ∀ T,
      costNumerator nextX Q x T ≤ costNumerator nextA P a T := by
  classical
  intro x a hr T
  induction T generalizing x a with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hq : Q x
      · rw [costNumerator_terminal nextX Q x hq (T + 1)]
        exact Nat.zero_le _
      · have hp : ¬ P a := fun h => hq (hstop x a hr h)
        rw [costNumerator_succ nextX Q x hq T,
          costNumerator_succ nextA P a hp T]
        have hh := ofFn_sum_le
          (fun e : Fin n => costNumerator nextX Q (nextX x e) T)
          (fun e : Fin n => costNumerator nextA P (nextA a e) T)
          (fun e => ih (nextX x e) (nextA a e)
            (hstep x a e hr hq hp))
        exact Nat.add_le_add_left hh (n ^ (T + 1))

/-- THE COST TRANSFER IS CONDITIONAL ON THE MISSING COMPLETE
physical stage simulation. No extra assumption is hidden.
Once discharged, the bound is exactly the abstract clock bound. -/
theorem resetClockStoppedCostOfSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsim : ResetClockExactPhysicalSimulation (q := q) ring root)
    (Czero : Config q n)
    (hlaunch : ResetLaunchPhysical ring Czero root)
    (T : Nat) :
    costNumerator (resetClockStoppedNext ring root)
      resetClockStoppedTarget (Czero, false) T ≤
      n ^ T * (n * (2 * (compileAdvice q).b - 1)) := by
  have hb : 2 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hr : resetClockStoppedRel ring root
      (Czero, false) (.outward 1) :=
    Or.inr ⟨hlaunch.1, resetClockLaunchStage ring Czero root hlaunch⟩
  have hcompare :=
    resetClockCostLeOfStoppedSimulation
      (resetClockStoppedNext ring root)
      (resetClockNext ring root (compileAdvice q).b)
      resetClockStoppedTarget
      (resetClockTerminal (compileAdvice q).b)
      (resetClockStoppedRel ring root)
      (fun x s hrel ht =>
        resetClockStoppedRelTerminal ring root x s hrel ht)
      (fun x s e hrel hx ht =>
        resetClockStoppedRelStep ring root hsim x s e hrel hx ht)
      (Czero, false) (.outward 1) hr T
  calc
    costNumerator (resetClockStoppedNext ring root)
        resetClockStoppedTarget (Czero, false) T ≤
        costNumerator (resetClockNext ring root (compileAdvice q).b)
          (resetClockTerminal (compileAdvice q).b) (.outward 1) T :=
      hcompare
    _ ≤ n ^ T * (n * (2 * (compileAdvice q).b - 1)) := by
      simpa only [resetClockRank] using
        (resetClockCost ring root (compileAdvice q).b hb
          (.outward 1) T)

/-- Also conditional: the cost-Numerator certificate upgrades to
the genuine uniform-IID first-hit expectation API. -/
theorem resetClockStoppedExpectedOfSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsim : ResetClockExactPhysicalSimulation (q := q) ring root)
    (Czero : Config q n)
    (hlaunch : ResetLaunchPhysical ring Czero root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockStoppedNext ring root)
      resetClockStoppedTarget (Czero, false)
      ((n * (2 * (compileAdvice q).b - 1) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (resetClockStoppedNext ring root)
    resetClockStoppedTarget ring.hn
    (Czero, false) (n * (2 * (compileAdvice q).b - 1))).2
  intro T
  exact resetClockStoppedCostOfSimulation ring root
    hsim Czero hlaunch T

end Counter
end L3

/-!
SMALL-mode counterexample to the stated, all-q
ResetClockExactPhysicalSimulation.

This section does not assert the false simulation theorem, nor any
unconditional stopped-cost bound.

The small-branch Base step preserves mode/bit/tok/lease but still
updates PACK. On a good internal edge the PACK role is fixed,
so a physically allowed nominated edge can leave the genuine
OUTWARD(1) stage unchanged while the abstract clock advances
to OUTWARD(2).
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- An explicit ring just large enough for the complete width
b=13 at q=2. -/
private def resetClockSmallRing : DirectedRing 14 :=
  ⟨by decide⟩

private def resetClockSmallRoot : Fin 14 :=
  ⟨0, by decide⟩

/-- A legal Cartesian configuration. The zero root waits with
the full 195-unit BANK lease; digit 1 has RR and zero bit.
All PACK roles are the corresponding site indices. In SMALL
mode these BANK fields are frozen, even on the nominated edge. -/
private def resetClockSmallConfiguration : Config 2 14 :=
  fun i =>
    { Agent.blank (compileAdvice 2) with
      pack := ⟨i.val, by
        change i.val < 15
        have hi : i.val < 14 := i.isLt
        omega⟩
      mode := .RWAIT
      lease := ⟨(compileAdvice 2).bankLeaseCap,
        Nat.lt_succ_self _⟩
      tok := if i.val = 1 then .RR else .E }

/-- Sites 0 through 13 do not wrap in the ring of length 14. -/
private theorem resetClockSmallSiteValue :
    ∀ j : Nat, j ≤ 13 →
      (site resetClockSmallRing resetClockSmallRoot j).val = j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hj
      have hk : k ≤ 13 := by omega
      have hlt : k + 1 < 14 := by omega
      change
        ((site resetClockSmallRing resetClockSmallRoot k).val + 1) %
          14 = k + 1
      rw [ih hk]
      exact Nat.mod_eq_of_lt hlt

private theorem resetClockSmallComplete :
    Complete resetClockSmallRing resetClockSmallConfiguration
      resetClockSmallRoot := by
  intro j hj
  have hbound : j ≤ 13 := by
    change j ≤ 13 at hj
    exact hj
  change (site resetClockSmallRing resetClockSmallRoot j).val = j
  exact resetClockSmallSiteValue j hbound

/-- This snapshot even satisfies the existing ResetLaunchPhysical
predicate, although it need not have a SMALL-mode launch history. -/
private theorem resetClockSmallLaunch :
    ResetLaunchPhysical resetClockSmallRing
      resetClockSmallConfiguration resetClockSmallRoot := by
  refine ⟨resetClockSmallComplete, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · constructor
    · rfl
    · change 0 < (compileAdvice 2).bankLeaseCap
      decide
  · rfl
  · change
      (if (site resetClockSmallRing resetClockSmallRoot 1).val = 1
        then BTok.RR else BTok.E) = BTok.RR
    rw [resetClockSmallSiteValue 1 (by decide)]
    decide
  · rfl

/-- The edge 1 -> 2 is genuinely admitted by ResetTrialAllowed:
its source/responder PACK roles already form a good pair, while
the root is fully framed. This uses the actual Protocol.step. -/
private theorem resetClockSmallAllowed :
    ResetTrialAllowed resetClockSmallRing resetClockSmallRoot
      resetClockSmallConfiguration
      (site resetClockSmallRing resetClockSmallRoot 1) := by
  have hc := resetClockSmallComplete
  have hroles := internal_roles_fixed resetClockSmallRing
    resetClockSmallConfiguration resetClockSmallRoot 1 hc
    (by decide)
  have hx : resetClockSmallRoot ≠
      site resetClockSmallRing resetClockSmallRoot 1 := by
    change site resetClockSmallRing resetClockSmallRoot 0 ≠
      site resetClockSmallRing resetClockSmallRoot 1
    exact resetCompleteSitesDifferent resetClockSmallRing
      resetClockSmallConfiguration resetClockSmallRoot hc
      0 1 (by decide) (by decide) (by decide)
  have hy : resetClockSmallRoot ≠
      resetClockSmallRing.rightNeighbor
        (site resetClockSmallRing resetClockSmallRoot 1) := by
    change site resetClockSmallRing resetClockSmallRoot 0 ≠
      site resetClockSmallRing resetClockSmallRoot 2
    exact resetCompleteSitesDifferent resetClockSmallRing
      resetClockSmallConfiguration resetClockSmallRoot hc
      0 2 (by decide) (by decide) (by decide)
  have hframe := step_frame resetClockSmallRing
    resetClockSmallConfiguration
    (site resetClockSmallRing resetClockSmallRoot 1)
    resetClockSmallRoot hx hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _
    exact congrFun hroles (site resetClockSmallRing resetClockSmallRoot j)
  · exact resetClockSmallLaunch.2.1
  · change
      (((protocol 2).step resetClockSmallRing
        resetClockSmallConfiguration
        (site resetClockSmallRing resetClockSmallRoot 1))
        resetClockSmallRoot).grant = false
    rw [hframe]
    exact resetClockSmallLaunch.2.1
  · change
      (((protocol 2).step resetClockSmallRing
        resetClockSmallConfiguration
        (site resetClockSmallRing resetClockSmallRoot 1))
        resetClockSmallRoot).mode = .RWAIT ∧
      0 <
      (((protocol 2).step resetClockSmallRing
        resetClockSmallConfiguration
        (site resetClockSmallRing resetClockSmallRoot 1))
        resetClockSmallRoot).lease.val
    rw [hframe]
    exact resetClockSmallLaunch.2.2.2.1

/-- A reusable obstruction: in SMALL mode, whenever OUTWARD(1)
and an allowed service of its nominated edge coexist, exact
simulation is impossible. This is not a hypothetical HOLD that
changes its physical stage: the physical stage HOLDS but the
abstract clock advances. -/
theorem resetClockSmallNominatedObstruction {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hsmall : (compileAdvice q).useSmall = true)
    (hc : Complete ring C root)
    (hs : resetClockStageAt ring C root (.outward 1))
    (ha : ResetTrialAllowed ring root C (site ring root 1)) :
    ¬ ResetClockExactPhysicalSimulation (q := q) ring root := by
  intro hsim
  have hb : 1 < (compileAdvice q).b :=
    resetTrialCompiledWidth q
  have hnt :
      ¬ resetClockTerminal (compileAdvice q).b (.outward 1) :=
    resetClockStageAtNotTerminal ring C root (.outward 1) hs
  have hnext :
      resetClockNext ring root (compileAdvice q).b
        (.outward 1) (site ring root 1) = .outward 2 := by
    simp [resetClockNext, resetClockNominated,
      resetClockAdvance, hnt, hb]
  let D : Config q n :=
    (protocol q).step ring C (site ring root 1)
  have hp : ResetTrialPhysical ring C root := Or.inl ⟨1, hs⟩
  have hn : 2 ≤ n := resetTrialMinRing ring C root hc hp
  have hfields : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit = (C (site ring root i)).bit ∧
      (D (site ring root i)).tok = (C (site ring root i)).tok := by
    intro i _ _
    have h := resetTrialSmallFieldsEverySite ring C
      (site ring root 1) (site ring root i) hn hsmall
    constructor
    · exact congrArg
        (fun z : Mode × Bool × BTok ×
          Fin ((compileAdvice q).bankLeaseCap + 1) => z.2.1) h
    · exact congrArg
        (fun z : Mode × Bool × BTok ×
          Fin ((compileAdvice q).bankLeaseCap + 1) => z.2.2.1) h
  have hstay : resetClockStageAt ring D root (.outward 1) :=
    resetClockStageAtDigitsCongr ring C D root
      ha.2.2.2 hfields (.outward 1) hs
  have hadvance :
      resetClockStageAt ring D root
        (resetClockNext ring root (compileAdvice q).b
          (.outward 1) (site ring root 1)) :=
    hsim C (.outward 1) (site ring root 1) hc hs ha
  rw [hnext] at hadvance
  change ResetOutwardPhysical ring D root 1 at hstay
  change ResetOutwardPhysical ring D root 2 at hadvance
  have hRR : (D (site ring root 1)).tok = .RR :=
    hstay.2.1.1.2.2
  have hE : (D (site ring root 1)).tok = .E :=
    (hadvance.2.1.2 1 (by omega) (by omega)).2
  rw [hRR] at hE
  cases hE

/-- A concrete refutation of the all-q simulation interface
in the existing Counter.lean. -/
theorem resetClockSmallNoExactSimulation :
    ¬ ResetClockExactPhysicalSimulation (q := 2)
      resetClockSmallRing resetClockSmallRoot := by
  exact resetClockSmallNominatedObstruction
    resetClockSmallRing resetClockSmallRoot
    resetClockSmallConfiguration
    (by decide)
    resetClockSmallComplete
    (resetClockLaunchStage resetClockSmallRing
      resetClockSmallConfiguration resetClockSmallRoot
      resetClockSmallLaunch)
    resetClockSmallAllowed

end Counter
end L3


/-!
BANK-only exact physical/abstract reset-clock simulation.

The SMALL counterexample to the unrestricted simulation (previous
section) remains. This block makes the restriction to the
spatial BANK branch explicit. It uses the previously proven literal BANK row certificates and the physical
stage-congruence lemma, not an assumed closure theorem.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- An authenticated stage is, in particular, a physical trial. -/
theorem resetClockStageToTrial {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s) :
    ResetTrialPhysical ring C root := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      exact Or.inl ⟨j, hs⟩
  | returning j =>
      exact Or.inr ⟨j, hs⟩

/-- A full-Agent frame on every active digit preserves the literal
OUTWARD(j) or RETURN(j) stage, rather than an existential stage. -/
theorem resetClockStageFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e)
    (hf : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root i) =
        C (site ring root i)) :
    resetClockStageAt ring ((protocol q).step ring C e) root s := by
  apply resetClockStageAtDigitsCongr ring C
    ((protocol q).step ring C e) root ha.2.2.2 ?_ s hs
  intro i hi hib
  have hcell := hf i hi hib
  exact ⟨congrArg (fun a : Agent (compileAdvice q) => a.bit) hcell,
    congrArg (fun a : Agent (compileAdvice q) => a.tok) hcell⟩

/-- Reusable exact-stage field custody for a selected internal pair.
The symbolic row has to return the OLD bit/token values at both
endpoints. All other active digits are fully framed. -/
theorem resetClockInternalPairStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C (site ring root k))
    (hrow :
      let x := site ring root k
      let y := site ring root (k + 1)
      let bx := bankCell (C x) k
      let byy := bankCell (C y) (k + 1)
      let z := bankPair bx byy (k + 1)
        (compileAdvice q).b (compileAdvice q).theta
      z.1.bit = (C x).bit ∧ z.1.tok = (C x).tok ∧
        z.2.bit = (C y).bit ∧ z.2.tok = (C y).tok) :
    resetClockStageAt ring
      ((protocol q).step ring C (site ring root k)) root s := by
  let x := site ring root k
  let y := site ring root (k + 1)
  let bx := bankCell (C x) k
  let byy := bankCell (C y) (k + 1)
  let z := bankPair bx byy (k + 1)
    (compileAdvice q).b (compileAdvice q).theta
  let D := (protocol q).step ring C x
  have hp : ResetTrialPhysical ring C root :=
    resetClockStageToTrial ring C root s hs
  have hpair :
      resetAgentBankTrip (D x) = resetCellBankTrip z.1 ∧
        resetAgentBankTrip (D y) = resetCellBankTrip z.2 :=
    resetTrialConsecutiveBankTrip ring C root hc hp hsp k (by omega)
  have hx := resetTrialTripBitTok (D x) z.1 hpair.1
  have hy := resetTrialTripBitTok (D y) z.2 hpair.2
  have hsx :
      (D x).bit = (C x).bit ∧ (D x).tok = (C x).tok :=
    ⟨hx.1.trans hrow.1, hx.2.trans hrow.2.1⟩
  have hsy :
      (D y).bit = (C y).bit ∧ (D y).tok = (C y).tok :=
    ⟨hy.1.trans hrow.2.2.1, hy.2.trans hrow.2.2.2⟩
  apply resetClockStageAtDigitsCongr ring C D root
    ha.2.2.2 ?_ s hs
  intro i hi hib
  by_cases hsource : i = k
  · subst i
    exact hsx
  · by_cases htarget : i = k + 1
    · subst i
      exact hsy
    · have hnotx : site ring root i ≠ x :=
        resetCompleteSitesDifferent ring C root hc i k
          hib (by omega) hsource
      have hnoty : site ring root i ≠
          ring.rightNeighbor x := by
        change site ring root i ≠ site ring root (k + 1)
        exact resetCompleteSitesDifferent ring C root hc
          i (k + 1) hib hkb htarget
      have hf := step_frame ring C x (site ring root i)
        hnotx hnoty
      exact ⟨congrArg
          (fun a : Agent (compileAdvice q) => a.bit) hf,
        congrArg (fun a : Agent (compileAdvice q) => a.tok) hf⟩

/-- Literal E/E swept internal HOLD, at the *same* stage. -/
theorem resetClockEmptyPairStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hleft :
      (C (site ring root k)).bit = false ∧
      (C (site ring root k)).tok = .E)
    (hright :
      (C (site ring root (k + 1))).bit = false ∧
      (C (site ring root (k + 1))).tok = .E)
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    resetClockStageAt ring
      ((protocol q).step ring C (site ring root k)) root s := by
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hrow := resetTrialBankEmptyHoldsSymbolic bx byy
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < (compileAdvice q).b; omega)
    (by rfl)
    (by change (C (site ring root k)).tok = .E; exact hleft.2)
    (by change (C (site ring root (k + 1))).tok = .E; exact hright.2)
    (by change (C (site ring root k)).bit = false; exact hleft.1)
    (by change (C (site ring root (k + 1))).bit = false; exact hright.1)
  apply resetClockInternalPairStageHold ring C root hc hsp
    s hs k hk hkb ha
  exact ⟨hrow.2.1.trans hleft.1.symm,
    hrow.1.trans hleft.2.symm,
    hrow.2.2.2.trans hright.1.symm,
    hrow.2.2.1.trans hright.2.symm⟩

/-- Non-top E/RR predecessor HOLD, at OUTWARD(k+1). -/
theorem resetClockOutwardPredecessorStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 < (compileAdvice q).b)
    (hout : ResetOutwardPhysical ring C root (k + 1))
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetOutwardPhysical ring
      ((protocol q).step ring C (site ring root k))
      root (k + 1) := by
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hleft := hout.2.1.2 k hk (by omega)
  have hrightTok : byy.tok = .RR := hout.2.1.1.2.2
  have hrightBit : byy.bit = false := hout.2.2
  have hrow := resetTrialBankPredecessorHoldsSymbolic
    bx byy (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < (compileAdvice q).b; omega)
    (by rfl)
    (by change k + 1 < (compileAdvice q).b; exact hkb)
    (by change (C (site ring root k)).tok = .E; exact hleft.2)
    hrightTok
    (by change (C (site ring root k)).bit = false; exact hleft.1)
    hrightBit
  exact resetClockInternalPairStageHold ring C root hc hsp
    (.outward (k + 1)) hout k hk (by omega) ha
    ⟨hrow.2.1.trans hleft.1.symm,
      hrow.1.trans hleft.2.symm,
      hrow.2.2.2.trans hrightBit.symm,
      hrow.2.2.1.trans hrightTok.symm⟩

/-- RL/E source HOLD, at RETURN(k), not RETURN(k-1). -/
theorem resetClockReturnSourceStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (k : Nat) (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice q).b)
    (hret : ResetReturnPhysical ring C root k)
    (ha : ResetTrialAllowed ring root C (site ring root k)) :
    ResetReturnPhysical ring
      ((protocol q).step ring C (site ring root k)) root k := by
  let bx := bankCell (C (site ring root k)) k
  let byy := bankCell (C (site ring root (k + 1))) (k + 1)
  have hright := hret.2.2.2 (k + 1)
    (by omega) hkb (by omega)
  have hleftTok : bx.tok = .RL := hret.2.1.2.2
  have hleftBit : bx.bit = false := hret.2.2.1
  have hrow := resetTrialBankReturnSourceHoldSymbolic
    bx byy (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ k; exact hk)
    (by change k < (compileAdvice q).b; omega)
    (by rfl) hleftTok hleftBit hright.2 hright.1
  exact resetClockInternalPairStageHold ring C root hc hsp
    (.returning k) hret k hk hkb ha
    ⟨hrow.2.1.trans hleftBit.symm,
      hrow.1.trans hleftTok.symm,
      hrow.2.2.2.trans hright.1.symm,
      hrow.2.2.1.trans hright.2.symm⟩

/-- Root RWAIT with digit one E/RR: every active digit bit/token
agrees with the old one, and the root is still waiting. -/
theorem resetClockRootOutgoingStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ha : ResetTrialAllowed ring root C root)
    (hbit : (C (site ring root 1)).bit = false)
    (htok : (C (site ring root 1)).tok = .E ∨
      (C (site ring root 1)).tok = .RR) :
    resetClockStageAt ring ((protocol q).step ring C root) root s := by
  have hp := resetClockStageToTrial ring C root s hs
  have hw : ResetRootWaiting C root := by
    cases s with
    | finished =>
        cases hs
    | outward j =>
        exact hs.1
    | returning j =>
        exact hs.1
  have hone := resetTrialRootOutWaitFields
    ring C root hc hp hsp ha hw hbit htok
  apply resetClockStageAtDigitsCongr ring C
    ((protocol q).step ring C root) root ha.2.2.2 ?_ s hs
  intro i hi hib
  by_cases hfirst : i = 1
  · subst i
    exact hone
  · have hlarge : 2 ≤ i := by omega
    have hf := resetTrialRootOutOtherDigitsFrame
      ring C root hc i hlarge hib
    exact ⟨congrArg
        (fun a : Agent (compileAdvice q) => a.bit) hf,
      congrArg (fun a : Agent (compileAdvice q) => a.tok) hf⟩

/-- Exact-stage preservation for a fully exterior edge. -/
theorem resetClockOutsideStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ha : ResetTrialAllowed ring root C e)
    (hout : OutsideSites q ring root e) :
    resetClockStageAt ring ((protocol q).step ring C e) root s := by
  apply resetClockStageFrame ring C root s hs e ha
  intro i _ hib
  exact outside_frame ring C root e hout i hib

/-- Incoming-root exterior edge: all positive digits are framed,
and next-cut root waiting comes from the allowed relation. -/
theorem resetClockIncomingRootStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ha : ResetTrialAllowed ring root C e)
    (hy : ring.rightNeighbor e = root)
    (hex : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b → e ≠ site ring root i) :
    resetClockStageAt ring ((protocol q).step ring C e) root s := by
  apply resetClockStageFrame ring C root s hs e ha
  intro i hi hib
  have hr : site ring root i ≠ root := by
    change site ring root i ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      i 0 hib (by omega) (by omega)
  have hx : site ring root i ≠ e := Ne.symm (hex i hi hib)
  have hyi : site ring root i ≠ ring.rightNeighbor e := by
    intro he
    exact hr (he.trans hy)
  exact step_frame ring C e (site ring root i) hx hyi

/-- All edges whose source is outside the complete active interval:
incoming-root and fully exterior services both preserve the exact
stage. This is the spatial cover's exterior half. -/
theorem resetClockNoActiveSourceStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ha : ResetTrialAllowed ring root C e)
    (hno : ∀ k : Nat, k ≤ (compileAdvice q).b →
      e ≠ site ring root k) :
    resetClockStageAt ring ((protocol q).step ring C e) root s := by
  by_cases hroot : ring.rightNeighbor e = root
  · exact resetClockIncomingRootStageHold
      ring C root e hc s hs ha hroot
      (fun i _ hib => hno i hib)
  · rcases resetTrialEdgeGeometry (q := q) ring root e with
        hsource | hincoming | houtside
    · obtain ⟨k, hk, he⟩ := hsource
      exact False.elim ((hno k hk) he)
    · exact False.elim (hroot hincoming)
    · exact resetClockOutsideStageHold
        ring C root e s hs ha houtside

/-- The top source has no IR in the physical BANK trial, hence
its own bit/token remain unchanged. No active positive digit is
its responder, even when the top source wraps into the root. -/
theorem resetClockTopSourceStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b))
    (hnoIR : (C (site ring root (compileAdvice q).b)).tok ≠ .IR) :
    resetClockStageAt ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root s := by
  let b := (compileAdvice q).b
  let e := site ring root b
  let y := ring.rightNeighbor e
  let bx := bankCell (C e) (C e).pack.val
  let byy := bankCell (C y) (C y).pack.val
  let z := bankPair bx byy (packNext bx.role byy.role b)
    b (compileAdvice q).theta
  let D := (protocol q).step ring C e
  have hp := resetClockStageToTrial ring C root s hs
  have hb : 0 < b := by
    have hh := resetTrialCompiledWidth q
    dsimp [b]
    omega
  have hrole : bx.role = b := hc b (by omega)
  have hbank : z.1.bit = bx.bit ∧ z.1.tok = bx.tok :=
    resetTrialBankTopSourceNoIR bx byy b
      (compileAdvice q).theta hrole hb hnoIR
  have hproj :
      resetAgentBankTrip (D e) = resetCellBankTrip z.1 :=
    (resetTrialSelectedBankTrip ring C root e hc hp hsp).1
  have hfields := resetTrialTripBitTok (D e) z.1 hproj
  have hsource :
      (D e).bit = (C e).bit ∧
        (D e).tok = (C e).tok :=
    ⟨hfields.1.trans hbank.1, hfields.2.trans hbank.2⟩
  apply resetClockStageAtDigitsCongr ring C D root
    ha.2.2.2 ?_ s hs
  intro i hi hib
  by_cases htop : i = b
  · subst i
    exact hsource
  · have hnotx : site ring root i ≠ e :=
      resetCompleteSitesDifferent ring C root hc i b
        hib (by omega) htop
    have hnoty : site ring root i ≠ y :=
      resetTrialTopResponderNotActive ring C root hc i hi hib
    have hf := step_frame ring C e (site ring root i)
      hnotx hnoty
    exact ⟨congrArg
        (fun a : Agent (compileAdvice q) => a.bit) hf,
      congrArg (fun a : Agent (compileAdvice q) => a.tok) hf⟩

/-- The top source edge HOLDS the topmost RR, rather than
performing the top turn. That turn is at the predecessor edge. -/
theorem resetClockTopOutwardStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hout : ResetOutwardPhysical ring C root
      (compileAdvice q).b)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b)) :
    ResetOutwardPhysical ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root
        (compileAdvice q).b := by
  have ht : (C (site ring root (compileAdvice q).b)).tok =
      .RR := hout.2.1.1.2.2
  apply resetClockTopSourceStageHold ring C root hc hsp
    (.outward (compileAdvice q).b) hout ha
  intro hbad
  rw [ht] at hbad
  cases hbad

/-- Every returning phase also has a non-IR top source, so
servicing it cannot move the RL to a different digit. -/
theorem resetClockTopReturnStageHold {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hret : ResetReturnPhysical ring C root j)
    (ha : ResetTrialAllowed ring root C
      (site ring root (compileAdvice q).b)) :
    ResetReturnPhysical ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root j := by
  have hnoIR :
      (C (site ring root (compileAdvice q).b)).tok ≠ .IR := by
    by_cases hj : j = (compileAdvice q).b
    · have ht : (C (site ring root (compileAdvice q).b)).tok =
          .RL := by
        rw [← hj]
        exact hret.2.1.2.2
      intro hbad
      rw [ht] at hbad
      cases hbad
    · have hb : 1 ≤ (compileAdvice q).b :=
        Nat.le_trans hret.2.1.1 hret.2.1.2.1
      have hclear := hret.2.2.2 (compileAdvice q).b
        hb (by omega) (Ne.symm hj)
      intro hbad
      rw [hclear.2] at hbad
      cases hbad
  exact resetClockTopSourceStageHold ring C root hc hsp
    (.returning j) hret ha hnoIR

/-- OUTWARD(j) HOLD for every non-nominated edge. Every branch
is an exact positional witness; in particular the E/RR predecessor
below the top is a HOLD, but the top predecessor is productive. -/
theorem resetClockOutwardIdleAllEdges {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hout : ResetOutwardPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e)
    (hnom : e ≠ resetClockNominated ring root
      (compileAdvice q).b (.outward j)) :
    ResetOutwardPhysical ring ((protocol q).step ring C e)
      root j := by
  let b := (compileAdvice q).b
  by_cases hsource : ∃ k : Nat, k ≤ b ∧ e = site ring root k
  · obtain ⟨k, hkb, he⟩ := hsource
    subst e
    by_cases hzero : k = 0
    · subst k
      have hfirst : 1 ≤ j := hout.2.1.1.1
      by_cases hjone : j = 1
      · subst j
        exact resetClockRootOutgoingStageHold ring C root hc
          hsp (.outward 1) hout ha hout.2.2
          (Or.inr hout.2.1.1.2.2)
      · have hbefore : 1 < j := by omega
        have hclear := hout.2.1.2 1 (by omega) hbefore
        exact resetClockRootOutgoingStageHold ring C root hc
          hsp (.outward j) hout ha hclear.1
          (Or.inl hclear.2)
    · have hkpos : 1 ≤ k := by omega
      by_cases htop : k = b
      · subst k
        by_cases hjtop : j = b
        · subst j
          exact resetClockTopOutwardStageHold ring C root hc
            hsp hout ha
        · have hjlt : j < b := by
            have hjbound := hout.2.1.1.2.1
            omega
          exact resetTrialAheadPreservesOutward
            ring C root hc j b hout ha hjlt (by omega)
      · have hklt : k < b := by omega
        by_cases hfar : k + 1 < j
        · have hx := hout.2.1.2 k hkpos (by omega)
          have hy := hout.2.1.2 (k + 1) (by omega) hfar
          exact resetClockEmptyPairStageHold ring C root hc hsp
            (.outward j) hout k hkpos (by omega) hx hy ha
        · by_cases hprev : k + 1 = j
          · by_cases hjtop : j = b
            · have hkm : k = b - 1 := by omega
              have hbad : site ring root k =
                  resetClockNominated ring root b (.outward j) := by
                rw [hjtop, hkm]
                simp [resetClockNominated]
              exact False.elim (hnom hbad)
            · have hnew : ResetOutwardPhysical ring C root (k + 1) := by
                rw [hprev]
                exact hout
              have hhold := resetClockOutwardPredecessorStageHold
                ring C root hc hsp k hkpos (by omega) hnew ha
              rw [hprev] at hhold
              exact hhold
          · by_cases hfront : k = j
            · have hjlt : j < b := by omega
              have hbad : site ring root k =
                  resetClockNominated ring root b (.outward j) := by
                rw [hfront]
                simp [resetClockNominated, hjlt]
              exact False.elim (hnom hbad)
            · have hahead : j < k := by omega
              exact resetTrialAheadPreservesOutward
                ring C root hc j k hout ha hahead hkb
  · have hno : ∀ k : Nat, k ≤ b →
        e ≠ site ring root k := by
      intro k hk he
      exact hsource ⟨k, hk, he⟩
    exact resetClockNoActiveSourceStageHold
      ring C root e hc (.outward j) hout ha hno

/-- RETURN(j) HOLD for every non-nominated edge. The only
productive return service is the predecessor-to-RL edge; an
RL-source outgoing edge is a HOLD. -/
theorem resetClockReturnIdleAllEdges {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hret : ResetReturnPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e)
    (hnom : e ≠ resetClockNominated ring root
      (compileAdvice q).b (.returning j)) :
    ResetReturnPhysical ring ((protocol q).step ring C e)
      root j := by
  let b := (compileAdvice q).b
  by_cases hsource : ∃ k : Nat, k ≤ b ∧ e = site ring root k
  · obtain ⟨k, hkb, he⟩ := hsource
    subst e
    by_cases hzero : k = 0
    · subst k
      by_cases hjone : j = 1
      · subst j
        exact False.elim (resetTrialRootRlTerminalExcluded
          ring C root hc hsp hret ha)
      · have hjpos := hret.2.1.1
        have hjbound := hret.2.1.2.1
        have hclear := hret.2.2.2 1
          (by omega) (by omega) (by omega)
        exact resetClockRootOutgoingStageHold ring C root hc
          hsp (.returning j) hret ha hclear.1
          (Or.inl hclear.2)
    · have hkpos : 1 ≤ k := by omega
      by_cases htop : k = b
      · subst k
        exact resetClockTopReturnStageHold
          ring C root hc hsp j hret ha
      · have hklt : k < b := by omega
        by_cases hprev : k + 1 = j
        · have hjgt : 1 < j := by omega
          have hkm : j - 1 = k := by omega
          have hbad : site ring root k =
              resetClockNominated ring root b (.returning j) := by
            simp [resetClockNominated, hjgt, hkm]
          exact False.elim (hnom hbad)
        · by_cases hfront : k = j
          · subst k
            exact resetClockReturnSourceStageHold
              ring C root hc hsp j (by omega) (by omega)
              hret ha
          · have hx : (C (site ring root k)).bit = false ∧
                (C (site ring root k)).tok = .E :=
              hret.2.2.2 k hkpos (by omega) hfront
            have hy : (C (site ring root (k + 1))).bit = false ∧
                (C (site ring root (k + 1))).tok = .E :=
              hret.2.2.2 (k + 1) (by omega)
                (by omega) hprev
            exact resetClockEmptyPairStageHold ring C root hc hsp
              (.returning j) hret k hkpos (by omega) hx hy ha
  · have hno : ∀ k : Nat, k ≤ b →
        e ≠ site ring root k := by
      intro k hk he
      exact hsource ⟨k, hk, he⟩
    exact resetClockNoActiveSourceStageHold
      ring C root e hc (.returning j) hret ha hno

/-- Full all-edge stage-exact outward simulation: the nominated
service advances the same physical front by one, or turns at the
top predecessor; every other allowed service is a positional HOLD. -/
theorem resetClockOutwardAllEdgesExact {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hout : ResetOutwardPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e) :
    resetClockStageAt ring ((protocol q).step ring C e) root
      (resetClockNext ring root (compileAdvice q).b
        (.outward j) e) := by
  let b := (compileAdvice q).b
  have hjpos : 1 ≤ j := hout.2.1.1.1
  have hjbound : j ≤ b := hout.2.1.1.2.1
  have hnt : ¬ resetClockTerminal b (.outward j) :=
    resetClockStageAtNotTerminal ring C root (.outward j) hout
  by_cases hnom : e = resetClockNominated ring root b (.outward j)
  · by_cases hjlt : j < b
    · have hsite : resetClockNominated ring root b (.outward j) =
          site ring root j := by
        simp [resetClockNominated, hjlt]
      have he : e = site ring root j := hnom.trans hsite
      subst he
      have hnext :
          resetClockNext ring root b (.outward j)
            (site ring root j) = .outward (j + 1) := by
        simp [resetClockNext, resetClockNominated,
          resetClockAdvance, hnt, hjlt]
      rw [show resetClockNext ring root (compileAdvice q).b (.outward j)
          (site ring root j) = .outward (j + 1) from hnext]
      exact resetClockPhysicalOutwardAdvance ring C root hc hsp
        j hout ha hjlt
    · have hjtop : j = b := by omega
      subst j
      have hsite : resetClockNominated ring root b (.outward b) =
          site ring root (b - 1) := by
        simp [resetClockNominated]
      have he : e = site ring root (b - 1) := hnom.trans hsite
      subst he
      have hnext :
          resetClockNext ring root b (.outward b)
            (site ring root (b - 1)) = .returning (b - 1) := by
        simp [resetClockNext, resetClockNominated,
          resetClockAdvance, hnt]
      rw [show resetClockNext ring root (compileAdvice q).b (.outward b)
          (site ring root (b - 1)) = .returning (b - 1) from hnext]
      exact resetClockPhysicalOutwardTurn ring C root hc hsp
        hout ha
  · have hnext :
        resetClockNext ring root b (.outward j) e = .outward j := by
      simp only [resetClockNext, if_neg hnt, if_neg hnom]
    rw [hnext]
    exact resetClockOutwardIdleAllEdges ring C root hc hsp
      j hout e ha hnom

/-- Full all-edge stage-exact return simulation: the nominated
predecessor edge retreats the RL by one; RETURN(1)'s nominated
root service is NOT allowed and is handled by the stopped chain. -/
theorem resetClockReturnAllEdgesExact {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hret : ResetReturnPhysical ring C root j)
    (e : Fin n) (ha : ResetTrialAllowed ring root C e) :
    resetClockStageAt ring ((protocol q).step ring C e) root
      (resetClockNext ring root (compileAdvice q).b
        (.returning j) e) := by
  let b := (compileAdvice q).b
  have hjpos : 1 ≤ j := hret.2.1.1
  have hjbound : j ≤ b := hret.2.1.2.1
  have hnt : ¬ resetClockTerminal b (.returning j) :=
    resetClockStageAtNotTerminal ring C root (.returning j) hret
  by_cases hnom : e = resetClockNominated ring root b (.returning j)
  · by_cases hjone : j = 1
    · subst j
      have hsite : resetClockNominated ring root b (.returning 1) =
          root := by
        simp [resetClockNominated]
      have he : e = root := hnom.trans hsite
      subst e
      exact False.elim (resetTrialRootRlTerminalExcluded
        ring C root hc hsp hret ha)
    · have hjgt : 1 < j := by omega
      have hsite :
          resetClockNominated ring root b (.returning j) =
            site ring root (j - 1) := by
        simp [resetClockNominated, hjgt]
      have he : e = site ring root (j - 1) := hnom.trans hsite
      subst he
      have hminus : j - 1 + 1 = j := by omega
      have hret' :
          ResetReturnPhysical ring C root (j - 1 + 1) := by
        rw [hminus]
        exact hret
      have hnext :
          resetClockNext ring root b (.returning j)
            (site ring root (j - 1)) = .returning (j - 1) := by
        simp [resetClockNext, resetClockNominated,
          resetClockAdvance, hnt, hjgt]
      rw [show resetClockNext ring root (compileAdvice q).b (.returning j)
          (site ring root (j - 1)) = .returning (j - 1) from hnext]
      exact resetClockPhysicalReturnRetreat ring C root hc hsp
        (j - 1) (by omega) (by omega) hret' ha
  · have hnext :
        resetClockNext ring root b (.returning j) e = .returning j := by
      simp only [resetClockNext, if_neg hnt, if_neg hnom]
    rw [hnext]
    exact resetClockReturnIdleAllEdges ring C root hc hsp
      j hret e ha hnom

/-- BANK-only formulation: unchanged old all-q definition, with
one explicit compile-time SMALL exclusion. -/
noncomputable def ResetClockBankSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  (compileAdvice q).useSmall = false →
    ResetClockExactPhysicalSimulation (q := q) ring root

/-- Exact BANK physical/abstract transition simulation for every
allowed edge, under the spatial compile branch. -/
theorem resetClockBankSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankSimulation (q := q) ring root := by
  intro hsp C s e hc hs ha
  cases s with
  | finished =>
      cases hs
  | outward j =>
      exact resetClockOutwardAllEdgesExact ring C root hc hsp
        j hs e ha
  | returning j =>
      exact resetClockReturnAllEdgesExact ring C root hc hsp
        j hs e ha

/-- A failure edge is sent to the absorbing physical STOP target.
No purported front stage is assigned to the disallowed successor. -/
theorem resetClockBankDisallowedStops {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n)
    (hna : ¬ ResetTrialAllowed ring root C e) :
    resetClockStoppedTarget
      (resetClockStoppedNext ring root (C, false) e) := by
  simp [resetClockStoppedNext, resetClockStoppedTarget, hna]

/-- The real terminal root-RL service is disallowed, arms the root,
and stops the actual chain; the abstract clock finishes. This
is outside the preterminal exact-simulation relation by design. -/
theorem resetClockBankFinalService {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : GrantFree C root)
    (hret : ResetReturnPhysical ring C root 1) :
    resetClockStoppedNext ring root (C, false) root =
        ((protocol q).step ring C root, true) ∧
      resetClockNext ring root (compileAdvice q).b
        (.returning 1) root = .finished ∧
      (((protocol q).step ring C root) root).mode = .ARMED := by
  have hna : ¬ ResetTrialAllowed ring root C root :=
    resetTrialRootRlTerminalExcluded ring C root hc hsp hret
  have hb : 2 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hstop :
      resetClockStoppedNext ring root (C, false) root =
        ((protocol q).step ring C root, true) := by
    simp [resetClockStoppedNext, hna]
  exact ⟨hstop,
    resetClockFinalNominated ring root (compileAdvice q).b hb,
    resetClockPhysicalFinalArms ring C root hc hsp hg hret⟩

/-- Unconditional-on-simulation finite-horizon stopped-attempt
cost in the BANK branch. The only hypotheses are the compile pin
and the existing physical launch snapshot. -/
theorem resetClockBankStoppedCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (Czero : Config q n)
    (hlaunch : ResetLaunchPhysical ring Czero root)
    (T : Nat) :
    costNumerator (resetClockStoppedNext ring root)
      resetClockStoppedTarget (Czero, false) T ≤
      n ^ T * (n * (2 * (compileAdvice q).b - 1)) := by
  exact resetClockStoppedCostOfSimulation ring root
    (resetClockBankSimulation (q := q) ring root hsp)
    Czero hlaunch T

/-- The genuine uniform-IID stopping-time expectation bound for
the actual BANK stopped trial; no hsim premise remains. -/
theorem resetClockBankStoppedExpected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (Czero : Config q n)
    (hlaunch : ResetLaunchPhysical ring Czero root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockStoppedNext ring root)
      resetClockStoppedTarget (Czero, false)
      ((n * (2 * (compileAdvice q).b - 1) : Nat) : Rat) := by
  exact resetClockStoppedExpectedOfSimulation ring root
    (resetClockBankSimulation (q := q) ring root hsp)
    Czero hlaunch

end Counter
end L3


/-!
One-step BANK stopped-exit classification and the boundary
role-defect obstruction to an unconditional C.2 renewal argument.

No claim is made that watchdog failure
mass controls all exits of the actual stopped chain.

The paper's C.2 renewal is for a role-stable counter interval. The
definition ResetTrialAllowed additionally checks role stability of
the selected edge. Completeness of sites 0..b alone does not constrain
the incoming-root predecessor's PACK role. An incoming defect can
therefore stop the actual chain before any watchdog timeout.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Exactly the rejected real-protocol services are one-step exits
of a live stopped attempt. The STOP flag does not distinguish a
completed reset from a role, grant, or waiting-mode failure. -/
theorem resetClockBankStopIffDisallowed {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) :
    resetClockStoppedTarget
      (resetClockStoppedNext ring root (C, false) e) ↔
      ¬ ResetTrialAllowed ring root C e := by
  classical
  by_cases ha : ResetTrialAllowed ring root C e
  · simp [resetClockStoppedNext, resetClockStoppedTarget, ha]
  · simp [resetClockStoppedNext, resetClockStoppedTarget, ha]

/-- Once STOP has been set, the stopped chain cannot start another
attempt: its transition is literally absorbing. A separate native
restart/retry construction is necessary for any renewal argument. -/
theorem resetClockBankStopAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (x : ResetClockStoppedState q n)
    (hstop : resetClockStoppedTarget x) :
    resetClockStoppedNext ring root x e = x := by
  simp [resetClockStoppedNext, resetClockStoppedTarget] at hstop ⊢
  simp [hstop]

/-- Exhaustive four-guard decomposition of a rejected edge. These
are precisely the four conjuncts in the existing definition of
ResetTrialAllowed, including the separate OLD and NEW grant tests. -/
theorem resetClockBankDisallowedGuardCases {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) :
    ¬ ResetTrialAllowed ring root C e ↔
      (¬ RoleStableEdge ring root C e ∨
        ¬ GrantFree C root ∨
        ¬ GrantFree ((protocol q).step ring C e) root ∨
        ¬ ResetRootWaiting ((protocol q).step ring C e) root) := by
  classical
  constructor
  · intro hbad
    by_cases hr : RoleStableEdge ring root C e
    · by_cases hg : GrantFree C root
      · by_cases hn : GrantFree ((protocol q).step ring C e) root
        · have hw :
            ¬ ResetRootWaiting ((protocol q).step ring C e) root := by
            intro hwait
            exact hbad ⟨hr, hg, hn, hwait⟩
          exact Or.inr (Or.inr (Or.inr hw))
        · exact Or.inr (Or.inr (Or.inl hn))
      · exact Or.inr (Or.inl hg)
    · exact Or.inl hr
  · intro h ha
    rcases h with hr | hg | hn | hw
    · exact hr ha.1
    · exact hg ha.2.1
    · exact hn ha.2.2.1
    · exact hw ha.2.2.2

/-- For an actual launch and its allowed continuations, OLD root
grant is false. At a STOP edge, only three failure-guard families
remain: role instability, a newly nonfree root grant, or loss of
RWAIT/positive lease (the last includes the matching final RL). -/
theorem resetClockBankStoppedLiveGuardCases {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hg : GrantFree C root)
    (hstop : resetClockStoppedTarget
      (resetClockStoppedNext ring root (C, false) e)) :
    ¬ RoleStableEdge ring root C e ∨
      ¬ GrantFree ((protocol q).step ring C e) root ∨
      ¬ ResetRootWaiting ((protocol q).step ring C e) root := by
  have hbad : ¬ ResetTrialAllowed ring root C e :=
    (resetClockBankStopIffDisallowed ring C root e).1 hstop
  have hguards :=
    (resetClockBankDisallowedGuardCases ring C root e).1 hbad
  rcases hguards with hr | hold | hnew | hwait
  · exact Or.inl hr
  · exact False.elim (hold hg)
  · exact Or.inr (Or.inl hnew)
  · exact Or.inr (Or.inr hwait)

/-- On an authenticated BANK stage, the one-step STOP exit is
classified as the genuine RETURN(1) root completion (which arms the
root), or as a rejected service with at least one of the three
non-old-grant guards violated. Failure is not equated to timeout. -/
theorem resetClockBankStoppedExitClassified {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n)
    (hstop : resetClockStoppedTarget
      (resetClockStoppedNext ring root (C, false) e)) :
    (e = root ∧ s = .returning 1 ∧
      (((protocol q).step ring C e) root).mode = .ARMED) ∨
    ((e ≠ root ∨ s ≠ .returning 1) ∧
      (¬ RoleStableEdge ring root C e ∨
        ¬ GrantFree ((protocol q).step ring C e) root ∨
        ¬ ResetRootWaiting ((protocol q).step ring C e) root)) := by
  have hguards :=
    resetClockBankStoppedLiveGuardCases ring C root e hg hstop
  by_cases he : e = root
  · by_cases hsfinal : s = .returning 1
    · have hret : ResetReturnPhysical ring C root 1 := by
        rw [hsfinal] at hs
        exact hs
      have hf := resetClockBankFinalService
        ring C root hc hsp hg hret
      have hmode :
          (((protocol q).step ring C e) root).mode = .ARMED := by
        rw [he]
        exact hf.2.2
      exact Or.inl ⟨he, hsfinal, hmode⟩
    · exact Or.inr ⟨Or.inr hsfinal, hguards⟩
  · exact Or.inr ⟨Or.inl he, hguards⟩

/-- A source whose PACK role is zero immediately to the left of
a complete root produces PACK role one at that root. The source
need not be inside the complete interval. This is a structural
projection of the real Protocol.step, not a BANK-only model. -/
theorem resetClockBankBadIncomingRootRole {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hne : root ≠ e)
    (hpred : ring.rightNeighbor e = root)
    (hsource : (C e).pack.val = 0) :
    (((protocol q).step ring C e) root).pack.val = 1 := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hrole :
      (((protocol q).step ring C e) root).pack.val =
        (roleWordStep (compileAdvice q).b ring
          (fun i => (C i).pack) e root).val :=
    congrArg Fin.val (congrFun (role_step ring C e) root)
  have hupdate :
      roleWordStep (compileAdvice q).b ring
        (fun i => (C i).pack) e root =
      roleUpdate (compileAdvice q).b (C e).pack (C root).pack := by
    simp [roleWordStep, hne, hpred]
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  calc
    (((protocol q).step ring C e) root).pack.val =
        (roleWordStep (compileAdvice q).b ring
          (fun i => (C i).pack) e root).val := hrole
    _ = (roleUpdate (compileAdvice q).b
          (C e).pack (C root).pack).val :=
      congrArg Fin.val hupdate
    _ = packNext (C e).pack.val (C root).pack.val
          (compileAdvice q).b :=
      roleUpdate_val (compileAdvice q).b (C e).pack (C root).pack
    _ = 1 := by
      rw [hsource, hroot]
      simp [packNext, hb]

/-- Such an incoming edge is a non-watchdog STOP. It destroys
Complete at the old root, hence the stopped successor cannot be
a fresh ResetLaunchPhysical at that root. The conclusion makes no
claim that the native protocol can never repair its roles later. -/
theorem resetClockBankBadIncomingRootExit {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hne : root ≠ e)
    (hpred : ring.rightNeighbor e = root)
    (hsource : (C e).pack.val = 0) :
    ¬ ResetTrialAllowed ring root C e ∧
      resetClockStoppedNext ring root (C, false) e =
        ((protocol q).step ring C e, true) ∧
      ¬ Complete ring ((protocol q).step ring C e) root ∧
      ¬ ResetLaunchPhysical ring ((protocol q).step ring C e) root := by
  let D := (protocol q).step ring C e
  have hnew : (D root).pack.val = 1 :=
    resetClockBankBadIncomingRootRole
      ring C root e hc hne hpred hsource
  have hold : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hbad : ¬ ResetTrialAllowed ring root C e := by
    intro ha
    have hstable : (D root).pack = (C root).pack := by
      simpa only [site] using ha.1 0 (by omega)
    have hv := congrArg Fin.val hstable
    omega
  have hnext :
      resetClockStoppedNext ring root (C, false) e =
        ((protocol q).step ring C e, true) := by
    simp [resetClockStoppedNext, hbad]
  have hnotcomplete : ¬ Complete ring D root := by
    intro hd
    have hz : (D root).pack.val = 0 := by
      simpa only [site] using hd 0 (by omega)
    omega
  refine ⟨hbad, hnext, hnotcomplete, ?_⟩
  intro hlaunch
  exact hnotcomplete hlaunch.1

/-- A bad exterior predecessor can be planted into the
twenty-site BANK example without touching the complete
root/digit interval. All coordinates remain legal Agent fields. -/
private def resetClockRenewalBadPrelaunch : Config 80 20 :=
  fun i =>
    if i = (19 : Fin 20) then
      { resetExampleConfig i with pack := ⟨0, by decide⟩ }
    else
      resetExampleConfig i

/-- The next snapshot is obtained by the ORIGINAL physical launch
edge 0 -> 1, rather than postulated as a valid launched state. -/
private def resetClockRenewalBadLaunched : Config 80 20 :=
  (protocol 80).step resetAliasRing
    resetClockRenewalBadPrelaunch (0 : Fin 20)

/-- The genuine launch supplies the full old physical launch
predicate, despite the unconstrained incoming-root predecessor. -/
private theorem resetClockRenewalBadLaunchPhysical :
    ResetLaunchPhysical resetAliasRing
      resetClockRenewalBadLaunched (0 : Fin 20) := by
  have hc : Complete resetAliasRing
      resetClockRenewalBadLaunched (0 : Fin 20) := by
    apply (resetCompleteIffFinite _ _ _).2
    apply resetCompleteCheckB_sound
    decide +kernel
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GrantFree; decide +kernel
  · decide +kernel
  · unfold ResetRootWaiting; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Explicit two-service trace: genuine BANK launch at edge zero
followed immediately by the incoming boundary edge nineteen.
At the failure cut the lease was at its full 260 units, the root
PACK is now 1, and the stopped successor is not a fresh launch.
The failure edge is NOT the terminal outgoing-root RL service. -/
theorem resetClockBankEarlyRoleFailureAfterLaunch :
    (compileAdvice 80).useSmall = false ∧
      ResetLaunchPhysical resetAliasRing
        resetClockRenewalBadLaunched (0 : Fin 20) ∧
      (resetClockRenewalBadLaunched (0 : Fin 20)).lease.val = 260 ∧
      resetClockStoppedNext resetAliasRing (0 : Fin 20)
        (resetClockRenewalBadLaunched, false) (19 : Fin 20) =
        ((protocol 80).step resetAliasRing
          resetClockRenewalBadLaunched (19 : Fin 20), true) ∧
      (((protocol 80).step resetAliasRing
        resetClockRenewalBadLaunched (19 : Fin 20))
          (0 : Fin 20)).pack.val = 1 ∧
      ¬ Complete resetAliasRing
        ((protocol 80).step resetAliasRing
          resetClockRenewalBadLaunched (19 : Fin 20))
        (0 : Fin 20) ∧
      ¬ ResetLaunchPhysical resetAliasRing
        ((protocol 80).step resetAliasRing
          resetClockRenewalBadLaunched (19 : Fin 20))
        (0 : Fin 20) ∧
      (19 : Fin 20) ≠ (0 : Fin 20) := by
  have hsp : (compileAdvice 80).useSmall = false := by
    decide +kernel
  have hlaunch := resetClockRenewalBadLaunchPhysical
  have hlease :
      (resetClockRenewalBadLaunched (0 : Fin 20)).lease.val = 260 := by
    decide +kernel
  have hne : (0 : Fin 20) ≠ (19 : Fin 20) := by
    decide
  have hpred :
      resetAliasRing.rightNeighbor (19 : Fin 20) =
        (0 : Fin 20) := by
    decide +kernel
  have hsource :
      (resetClockRenewalBadLaunched (19 : Fin 20)).pack.val = 0 := by
    decide +kernel
  have hrole := resetClockBankBadIncomingRootRole
    resetAliasRing resetClockRenewalBadLaunched
    (0 : Fin 20) (19 : Fin 20)
    hlaunch.1 hne hpred hsource
  have hresult := resetClockBankBadIncomingRootExit
    resetAliasRing resetClockRenewalBadLaunched
    (0 : Fin 20) (19 : Fin 20)
    hlaunch.1 hne hpred hsource
  exact ⟨hsp, hlaunch, hlease, hresult.2.1,
    hrole, hresult.2.2.1, hresult.2.2.2, Ne.symm hne⟩

end Counter
end L3


/-!
The role-stable BANK comparison, first local layer.

A supported bad PACK pair (including the outside predecessor/source
at the incoming-root seam or the top responder) is a defect exit of
the FROZEN comparison, not a watchdog failure. A selected service
that changes any root/digit PACK role is also a defect exit.

The ResetTrialAllowed check is unchanged, and
the new comparison uses the same real Protocol.step for its physical
coordinate. Its exit label distinguishes defect, authentic root-RL
success, root grant, and loss of positive RWAIT. In particular
the latter is deliberately named waitLoss, not watchdog: the exact
equivalence with exhausted BANK lease needs a separate root-lease
projection theorem and is NOT silently asserted below.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The selected edge lies in the counter's causal support and
either has a bad OLD PACK pair or changes a protected PACK role.
The bad-pair clause detects the boundary repair of an exterior
responder even when no protected role changes yet. -/
def ResetClockBankDefectEntry {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) : Prop :=
  Support q ring root e ∧
    (goodPair (compileAdvice q).b
        (C e).pack (C (ring.rightNeighbor e)).pack = false ∨
      ¬ RoleStableEdge ring root C e)

/-- Any edge that changes a protected role must lie in S_r.
In the alternative case both endpoints are outside sites 0..b,
so the full actual Protocol.step frame forces role stability. -/
theorem resetClockBankUnstableSupported {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hbad : ¬ RoleStableEdge ring root C e) :
    Support q ring root e := by
  by_cases hs : Support q ring root e
  · exact hs
  · rcases resetTrialEdgeGeometry (q := q) ring root e with
        hsource | hincoming | houtside
    · obtain ⟨k, hk, he⟩ := hsource
      exact False.elim (hs (Or.inr ⟨k, hk, he⟩))
    · exact False.elim (hs (Or.inl hincoming))
    · have hstable : RoleStableEdge ring root C e := by
        intro j hj
        have hf := outside_frame ring C root e houtside j hj
        exact congrArg
          (fun a : Agent (compileAdvice q) => a.pack) hf
      exact False.elim (hbad hstable)

/-- A failure of RoleStableEdge is always recorded as a defect,
without requiring an additional assumption about outside roles. -/
theorem resetClockBankDefectOfUnstable {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hbad : ¬ RoleStableEdge ring root C e) :
    ResetClockBankDefectEntry ring C root e := by
  exact ⟨resetClockBankUnstableSupported ring C root e hbad,
    Or.inr hbad⟩

/-- A supported OLD bad pair is detected as a defect even when
the repair first changes an exterior PACK role. -/
theorem resetClockBankDefectOfBadPair {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsupport : Support q ring root e)
    (hbad : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = false) :
    ResetClockBankDefectEntry ring C root e := by
  exact ⟨hsupport, Or.inl hbad⟩

/-- No detected defect is strong enough to discharge the literal
role-stability conjunct of ResetTrialAllowed on any selected edge. -/
theorem resetClockBankStableOfNoDefect {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hno : ¬ ResetClockBankDefectEntry ring C root e) :
    RoleStableEdge ring root C e := by
  by_cases hstable : RoleStableEdge ring root C e
  · exact hstable
  · exact False.elim
      (hno (resetClockBankDefectOfUnstable ring C root e hstable))

/-- The earlier incoming-root counterexample is now
classified as a SUPPORT defect, rather than a watchdog exit. -/
theorem resetClockBankIncomingBadRoleTagged {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hne : root ≠ e)
    (hpred : ring.rightNeighbor e = root)
    (hsource : (C e).pack.val = 0) :
    ResetClockBankDefectEntry ring C root e := by
  have hnew : (((protocol q).step ring C e) root).pack.val = 1 :=
    resetClockBankBadIncomingRootRole
      ring C root e hc hne hpred hsource
  have hold : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hnotStable : ¬ RoleStableEdge ring root C e := by
    intro hs
    have hv := congrArg Fin.val (hs 0 (by omega))
    change (((protocol q).step ring C e) root).pack.val =
      (C root).pack.val at hv
    omega
  exact ⟨Or.inl hpred, Or.inr hnotStable⟩

/-- The earlier two-service concrete witness is a defect at the
root's incoming boundary. -/
theorem resetClockBankEarlyRoleExitIsDefect :
    ResetClockBankDefectEntry resetAliasRing
      resetClockRenewalBadLaunched (0 : Fin 20) (19 : Fin 20) := by
  have hc := resetClockRenewalBadLaunchPhysical.1
  have hne : (0 : Fin 20) ≠ (19 : Fin 20) := by
    decide
  have hpred :
      resetAliasRing.rightNeighbor (19 : Fin 20) =
        (0 : Fin 20) := by
    decide +kernel
  have hsource :
      (resetClockRenewalBadLaunched (19 : Fin 20)).pack.val = 0 := by
    decide +kernel
  exact resetClockBankIncomingBadRoleTagged
    resetAliasRing resetClockRenewalBadLaunched
    (0 : Fin 20) (19 : Fin 20)
    hc hne hpred hsource

/-- The comparison has a fifth LIVE label, and four disjoint
exit labels. waitLoss means the RWAIT-positive-lease predicate
failed; it is NOT yet identified with an exhausted BANK lease. -/
inductive ResetClockBankExit where
  | live
  | success
  | waitLoss
  | grant
  | defect
  deriving DecidableEq, Repr

/-- Priority: boundary defect, actual RETURN(1) root completion,
new root grant, loss of RWAIT/positive lease, or live continuation.
The successor is always calculated using the ACTUAL protocol. -/
noncomputable def resetClockBankOutcome {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (s : ResetClockStage) (e : Fin n) :
    ResetClockBankExit :=
  if ResetClockBankDefectEntry ring C root e then .defect
  else if e = root ∧ s = .returning 1 then .success
  else if ¬ GrantFree ((protocol q).step ring C e) root then .grant
  else if ¬ ResetRootWaiting ((protocol q).step ring C e) root then .waitLoss
  else .live

/-- Real physical state, abstract phase, and the absorbing
comparison exit. No change to the original stopped-chain API. -/
abbrev ResetClockBankComparisonState (q n : Nat) :=
  (Config q n × ResetClockStage) × ResetClockBankExit

/-- One comparison transition. Defect entry stops the frozen
comparison rather than being charged as a failed BANK worker.
The physical projection of a LIVE transition is Protocol.step. -/
noncomputable def resetClockBankComparisonNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n) (e : Fin n) :
    ResetClockBankComparisonState q n :=
  if x.2 = .live then
    (((protocol q).step ring x.1.1 e,
       resetClockNext ring root (compileAdvice q).b x.1.2 e),
      resetClockBankOutcome ring root x.1.1 x.1.2 e)
  else x

/-- Any of the four exits is absorbing in the comparison. -/
theorem resetClockBankComparisonExitAbsorbing {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hstop : x.2 ≠ .live) :
    resetClockBankComparisonNext ring root x e = x := by
  simp [resetClockBankComparisonNext, hstop]

/-- The comparison does not fabricate physical BANK transitions.
At a live cut it projects to the same selected physical edge as
the existing resetClockStoppedNext, even when the latter stops. -/
theorem resetClockBankComparisonPhysicalStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (s : ResetClockStage) :
    (resetClockBankComparisonNext ring root
      ((C, s), .live) e).1.1 =
      (resetClockStoppedNext ring root (C, false) e).1 := by
  change (protocol q).step ring C e =
    (resetClockStoppedNext ring root (C, false) e).1
  by_cases ha : ResetTrialAllowed ring root C e
  · simp [resetClockStoppedNext, ha]
  · simp [resetClockStoppedNext, ha]

/-- On an actual preterminal physical phase, a loss of root waiting
can only occur at one of the two root-incident edges. This is
not yet a proof that the OLD lease was one. -/
theorem resetClockBankWaitLossIncident {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hlose : ¬ ResetRootWaiting ((protocol q).step ring C e) root) :
    e = root ∨ ring.rightNeighbor e = root := by
  have hw : ResetRootWaiting C root := by
    cases s with
    | finished =>
        cases hs
    | outward j =>
        exact hs.1
    | returning j =>
        exact hs.1
  by_cases hx : e = root
  · exact Or.inl hx
  · by_cases hy : ring.rightNeighbor e = root
    · exact Or.inr hy
    · have hf := step_frame ring C e root
        (Ne.symm hx) (Ne.symm hy)
      have hwnew :
          ResetRootWaiting ((protocol q).step ring C e) root := by
        unfold ResetRootWaiting at hw ⊢
        rw [hf]
        exact hw
      exact False.elim (hlose hwnew)

/-- The exact mutually exclusive outcome classifier is extracted
directly from the comparison's priority test. An authentic success
is validated by the existing BANK final-arm/root-RL theorem. -/
theorem resetClockBankOutcomeCases {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n) :
    resetClockBankOutcome ring root C s e = .live ∨
    (resetClockBankOutcome ring root C s e = .defect ∧
      ResetClockBankDefectEntry ring C root e) ∨
    (resetClockBankOutcome ring root C s e = .success ∧
      e = root ∧ s = .returning 1 ∧
      (((protocol q).step ring C e) root).mode = .ARMED ∧
      resetClockNext ring root (compileAdvice q).b s e = .finished) ∨
    (resetClockBankOutcome ring root C s e = .grant ∧
      ¬ GrantFree ((protocol q).step ring C e) root) ∨
    (resetClockBankOutcome ring root C s e = .waitLoss ∧
      ¬ ResetRootWaiting ((protocol q).step ring C e) root) := by
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · have hclass : resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hd]
    exact Or.inr (Or.inl ⟨hclass, hd⟩)
  · by_cases hf : e = root ∧ s = .returning 1
    · have hclass : resetClockBankOutcome ring root C s e = .success := by
        simp [resetClockBankOutcome, hd, hf,
          show ¬ ResetClockBankDefectEntry ring C root root from hf.1 ▸ hd]
      have hret : ResetReturnPhysical ring C root 1 := by
        have hphase := hs
        rw [hf.2] at hphase
        exact hphase
      have hmode :
          (((protocol q).step ring C e) root).mode = .ARMED := by
        rw [hf.1]
        exact (resetClockBankFinalService
          ring C root hc hsp hg hret).2.2
      have hb : 2 ≤ (compileAdvice q).b := by
        have hw := resetTrialCompiledWidth q
        omega
      have hfinished :
          resetClockNext ring root (compileAdvice q).b s e =
            .finished := by
        rw [hf.1, hf.2]
        exact resetClockFinalNominated ring root
          (compileAdvice q).b hb
      exact Or.inr (Or.inr (Or.inl
        ⟨hclass, hf.1, hf.2, hmode, hfinished⟩))
    · by_cases hgnew : GrantFree ((protocol q).step ring C e) root
      · by_cases hwnew : ResetRootWaiting ((protocol q).step ring C e) root
        · have hclass : resetClockBankOutcome ring root C s e =
              .live := by
            simp [resetClockBankOutcome, hd, hf, hgnew, hwnew]
          exact Or.inl hclass
        · have hclass : resetClockBankOutcome ring root C s e =
              .waitLoss := by
            simp [resetClockBankOutcome, hd, hf, hgnew, hwnew]
          exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hclass, hwnew⟩)))
      · have hclass : resetClockBankOutcome ring root C s e =
            .grant := by
          simp [resetClockBankOutcome, hd, hf, hgnew]
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hclass, hgnew⟩)))

/-- A live outcome necessarily passed all four conjuncts of
ResetTrialAllowed. Hence the BANK simulation theorem, already
proved above, supplies the exact next stage. -/
theorem resetClockBankOutcomeLiveAllowed {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n)
    (hlive : resetClockBankOutcome ring root C s e = .live) :
    ResetTrialAllowed ring root C e ∧
      Complete ring ((protocol q).step ring C e) root ∧
      resetClockStageAt ring ((protocol q).step ring C e) root
        (resetClockNext ring root (compileAdvice q).b s e) := by
  have hd : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hbad
    have hclass :
        resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hbad]
    rw [hclass] at hlive
    cases hlive
  have hf : ¬ (e = root ∧ s = .returning 1) := by
    intro hfinal
    have hclass :
        resetClockBankOutcome ring root C s e = .success := by
      simp [resetClockBankOutcome, hd, hfinal,
        show ¬ ResetClockBankDefectEntry ring C root root from hfinal.1 ▸ hd]
    rw [hclass] at hlive
    cases hlive
  have hgnew : GrantFree ((protocol q).step ring C e) root := by
    by_cases hnew : GrantFree ((protocol q).step ring C e) root
    · exact hnew
    · have hclass :
          resetClockBankOutcome ring root C s e = .grant := by
        simp [resetClockBankOutcome, hd, hf, hnew]
      rw [hclass] at hlive
      cases hlive
  have hwnew : ResetRootWaiting ((protocol q).step ring C e) root := by
    by_cases hnew : ResetRootWaiting ((protocol q).step ring C e) root
    · exact hnew
    · have hclass :
          resetClockBankOutcome ring root C s e = .waitLoss := by
        simp [resetClockBankOutcome, hd, hf, hgnew, hnew]
      rw [hclass] at hlive
      cases hlive
  have hrole : RoleStableEdge ring root C e :=
    resetClockBankStableOfNoDefect ring C root e hd
  have ha : ResetTrialAllowed ring root C e :=
    ⟨hrole, hg, hgnew, hwnew⟩
  have hsim : ResetClockExactPhysicalSimulation (q := q) ring root :=
    resetClockBankSimulation (q := q) ring root hsp
  exact ⟨ha,
    resetTrialAllowedComplete ring C root e hc ha,
    hsim C s e hc hs ha⟩

/-- At a live comparison cut the physical state is complete,
grant-free, and matches its single abstract preterminal stage. -/
def ResetClockBankComparisonGood {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n) : Prop :=
  x.2 = .live →
    Complete ring x.1.1 root ∧
      GrantFree x.1.1 root ∧
      resetClockStageAt ring x.1.1 root x.1.2

/-- The genuine launch snapshot initializes the comparison. -/
theorem resetClockBankComparisonGoodLaunch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hlaunch : ResetLaunchPhysical ring C root) :
    ResetClockBankComparisonGood ring root ((C, .outward 1), .live) := by
  intro _
  exact ⟨hlaunch.1, hlaunch.2.1,
    resetClockLaunchStage ring C root hlaunch⟩

/-- On a live comparison successor, the earlier kernel-checked
BANK simulation recovers completeness, grant freedom and the
identical abstract stage. An exit remains absorbing and needs
no new stage assertion. -/
theorem resetClockBankComparisonGoodStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankComparisonState q n)
    (hgood : ResetClockBankComparisonGood ring root x)
    (e : Fin n) :
    ResetClockBankComparisonGood ring root
      (resetClockBankComparisonNext ring root x e) := by
  intro hnextLive
  by_cases hx : x.2 = .live
  · obtain ⟨hc, hg, hs⟩ := hgood hx
    let C := x.1.1
    let s := x.1.2
    have hnext :
        resetClockBankComparisonNext ring root x e =
          (((protocol q).step ring C e,
            resetClockNext ring root (compileAdvice q).b s e),
            resetClockBankOutcome ring root C s e) := by
      simp [resetClockBankComparisonNext, hx, C, s]
    have hlive :
        resetClockBankOutcome ring root C s e = .live := by
      rw [hnext] at hnextLive
      exact hnextLive
    obtain ⟨ha, hcomplete, hstage⟩ :=
      resetClockBankOutcomeLiveAllowed
        ring C root hsp hc hg s hs e hlive
    rw [hnext]
    exact ⟨hcomplete, ha.2.2.1, hstage⟩
  · have hnext :
        resetClockBankComparisonNext ring root x e = x := by
      simp [resetClockBankComparisonNext, hx]
    rw [hnext] at hnextLive
    exact False.elim (hx hnextLive)

/-- Actual word of independent scheduled edges, with an absorbing
comparison exit and the exact real-protocol physical projection. -/
noncomputable def resetClockBankComparisonWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → ResetClockBankComparisonState q n →
      ResetClockBankComparisonState q n
  | [], x => x
  | e :: es, x =>
      resetClockBankComparisonWord ring root es
        (resetClockBankComparisonNext ring root x e)

/-- Every finite edge word stays in the live physical/abstract
relation until its first independently classified comparison exit. -/
theorem resetClockBankComparisonGoodWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (w : List (Fin n)) (x : ResetClockBankComparisonState q n),
      ResetClockBankComparisonGood ring root x →
      ResetClockBankComparisonGood ring root
        (resetClockBankComparisonWord ring root w x) := by
  intro w
  induction w with
  | nil =>
      intro x hx
      exact hx
  | cons e es ih =>
      intro x hx
      change ResetClockBankComparisonGood ring root
        (resetClockBankComparisonWord ring root es
          (resetClockBankComparisonNext ring root x e))
      exact ih _
        (resetClockBankComparisonGoodStep ring root hsp x hx e)

end Counter
end L3


/-!
Root BANK lease projection and exact wait-loss criterion.

The role-stable comparison and the incoming-root defect witness
are proved above. Only the first requested task is attacked in this block. C.1 and
C.2 require additional probabilistic / retry-kernel certificates.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- A BANK owner lease within the compiled cap is copied literally. -/
theorem resetClockCopyBankLeaseExact {c : Compiled}
    (a : Agent c) (z : BankCell)
    (hz : z.lease < c.bankLeaseCap + 1) :
    (copyBank a z).lease.val = z.lease := by
  simp [copyBank, hz]

/-- CopyBank's lease does not depend on the other Base owner
fields. This is the missing fourth BANK-coordinate projection,
expressed without an unjustified global bound on every BankCell. -/
theorem resetClockBaseLeasePair (c : Compiled)
    (ev : CertEvent) (x y : Agent c)
    (hsp : c.useSmall = false) :
    (baseStep c ev x y).1.lease =
      (copyBank x (resetBankOld x y).1).lease ∧
    (baseStep c ev x y).2.lease =
      (copyBank y (resetBankOld x y).2).lease := by
  constructor
  · simp [baseStep, hsp, resetBankOld, copyBank,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | rfl | split)
  · simp [baseStep, hsp, resetBankOld, copyBank,
      Agent.setNative, Agent.setCPriv] <;>
      repeat (first | rfl | split)

/-- Certificate/HK assembly never writes the BANK lease. -/
theorem resetClockTransitionLeasePair (c : Compiled)
    (x y : Agent c) (hsp : c.useSmall = false) :
    (transition c x y).1.lease =
      (copyBank x (resetBankOld x y).1).lease ∧
    (transition c x y).2.lease =
      (copyBank y (resetBankOld x y).2).lease := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := resetClockBaseLeasePair c ev x y hsp
  simpa [transition, hc, hh, assemble] using hb

/-- Lease projection for the real selected directed-ring edge. -/
theorem resetClockPhysicalEdgeLeasePair {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C e) e).lease =
      (copyBank (C e)
        (resetBankOld (C e) (C (ring.rightNeighbor e))).1).lease ∧
    (((protocol q).step ring C e)
      (ring.rightNeighbor e)).lease =
      (copyBank (C (ring.rightNeighbor e))
        (resetBankOld (C e) (C (ring.rightNeighbor e))).2).lease := by
  have hh := resetClockTransitionLeasePair (compileAdvice q)
    (C e) (C (ring.rightNeighbor e)) hsp
  simpa [PopulationProtocol.step, protocol, hne] using hh

/-- Waiting root service: one lease tick, resetting exactly at
one remaining unit. -/
def resetClockWaitMode (lease : Nat) : Mode :=
  if 1 < lease then .RWAIT else .RESET

def resetClockWaitLease (lease : Nat) : Nat :=
  if 1 < lease then lease - 1 else 0

/-- Incoming-root RWAIT row, with stable role zero at the responder.
The symbolic source is any nonroot BANK cell. -/
theorem resetClockIncomingWaitSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false) (hm : y.mode = .RWAIT) :
    let z := bankPair x y 0 b theta
    z.2.mode = resetClockWaitMode y.lease ∧
      z.2.lease = resetClockWaitLease y.lease := by
  by_cases hl : 1 < y.lease
  · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
      hx, hy, hg, hm, hl, isWaitMode] <;>
      repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)
  · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
      hx, hy, hg, hm, hl, isWaitMode] <;>
      repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)

/-- Outgoing RWAIT/E and RWAIT/RR services tick the lease.
The first-digit RL service is excluded: it instead arms the root. -/
theorem resetClockOutgoingWaitSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .RWAIT)
    (hb : 1 < b)
    (ht : y.tok = .E ∨ y.tok = .RR) :
    let z := bankPair x y 1 b theta
    z.1.mode = resetClockWaitMode x.lease ∧
      z.1.lease = resetClockWaitLease x.lease := by
  have hbge : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  rcases ht with he | hr
  · by_cases hl : 1 < x.lease
    · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
        hx, hy, hg, hm, hbge, hbne, he, hl,
        isRetTok, isWaitMode] <;>
        repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)
    · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
        hx, hy, hg, hm, hbge, hbne, he, hl,
        isRetTok, isWaitMode] <;>
        repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)
  · by_cases hl : 1 < x.lease
    · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
        hx, hy, hg, hm, hbge, hbne, hr, hl,
        isRetTok, isWaitMode] <;>
        repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)
    · simp [bankPair, resetClockWaitMode, resetClockWaitLease,
        hx, hy, hg, hm, hbge, hbne, hr, hl,
        isRetTok, isWaitMode] <;>
        repeat (first | exact ⟨rfl, rfl⟩ | rfl | split)

/-- Conversion from the numeric owner WAIT fields to the exact
physical waiting predicate. -/
theorem resetClockWaitFieldsIff {n q : Nat}
    (C D : Config q n) (root : Fin n)
    (hmode : (D root).mode =
      resetClockWaitMode (C root).lease.val)
    (hlease : (D root).lease.val =
      resetClockWaitLease (C root).lease.val) :
    ResetRootWaiting D root ↔ 1 < (C root).lease.val := by
  constructor
  · intro hw
    by_cases hl : 1 < (C root).lease.val
    · exact hl
    · have hm := hw.1
      rw [hmode] at hm
      simp [resetClockWaitMode, hl] at hm
  · intro hl
    unfold ResetRootWaiting
    constructor
    · rw [hmode]
      simp [resetClockWaitMode, hl]
    · rw [hlease]
      simp only [resetClockWaitLease, if_pos hl]
      omega

/-- The new lease lies in the physical Fin carrier whenever the
old lease does, including the timeout-to-zero branch. -/
theorem resetClockWaitLeaseFits {c : Compiled}
    (a : Agent c) :
    resetClockWaitLease a.lease.val < c.bankLeaseCap + 1 := by
  by_cases hl : 1 < a.lease.val
  · simp only [resetClockWaitLease, if_pos hl]
    have hb := a.lease.isLt
    omega
  · simp [resetClockWaitLease, hl]

/-- The real outgoing root RWAIT/E or RWAIT/RR service, including
the exact physical lease. The physical-stage witness supplies
the nontrivial minimum-ring premise needed by the endpoint API. -/
theorem resetClockOutgoingWaitPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : GrantFree C root)
    (hw : ResetRootWaiting C root)
    (ht : (C (site ring root 1)).tok = .E ∨
      (C (site ring root 1)).tok = .RR) :
    (((protocol q).step ring C root) root).mode =
        resetClockWaitMode (C root).lease.val ∧
      (((protocol q).step ring C root) root).lease.val =
        resetClockWaitLease (C root).lease.val := by
  have hb : 1 < (compileAdvice q).b :=
    resetTrialCompiledWidth q
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone :
      (C (ring.rightNeighbor root)).pack.val = 1 := by
    simpa only [site] using hc 1 (by omega)
  have hpost :
      packNext (C root).pack.val
        (C (ring.rightNeighbor root)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
    intro h0
    exact absurd h0 (by omega)
  have hrow :
      ((resetBankOld (C root)
        (C (ring.rightNeighbor root))).1).mode =
          resetClockWaitMode (C root).lease.val ∧
      ((resetBankOld (C root)
        (C (ring.rightNeighbor root))).1).lease =
          resetClockWaitLease (C root).lease.val := by
    have hh := resetClockOutgoingWaitSymbolic
      (bankCell (C root) (C root).pack.val)
      (bankCell (C (ring.rightNeighbor root))
        (C (ring.rightNeighbor root)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C (ring.rightNeighbor root)).pack.val = 1; exact hone)
      (by change (C root).grant = false; exact hg)
      (by change (C root).mode = .RWAIT; exact hw.1)
      hb (by simpa only [site, bankCell] using ht)
    simpa only [resetBankOld, hpost, bankCell] using hh
  have hn : 2 ≤ n := resetTrialMinRing ring C root hc hp
  have hmodeProjection := congrArg
    (fun z : Mode × Bool × BTok => z.1)
    ((resetPhysicalEdgeBankTrip ring C root
      (resetRootPortDistinct ring root hn) hsp).1)
  change (((protocol q).step ring C root) root).mode =
    ((resetBankOld (C root)
      (C (ring.rightNeighbor root))).1).mode at hmodeProjection
  have hleaseProjection :=
    (resetClockPhysicalEdgeLeasePair ring C root
      (resetRootPortDistinct ring root hn) hsp).1
  have hbound :
      ((resetBankOld (C root)
        (C (ring.rightNeighbor root))).1).lease <
        (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2]
    exact resetClockWaitLeaseFits (C root)
  have hcopy :=
    resetClockCopyBankLeaseExact (C root)
      ((resetBankOld (C root)
        (C (ring.rightNeighbor root))).1) hbound
  have hlease :
      (((protocol q).step ring C root) root).lease.val =
        resetClockWaitLease (C root).lease.val := by
    calc
      (((protocol q).step ring C root) root).lease.val =
          (copyBank (C root)
            ((resetBankOld (C root)
              (C (ring.rightNeighbor root))).1)).lease.val :=
        congrArg Fin.val hleaseProjection
      _ = ((resetBankOld (C root)
            (C (ring.rightNeighbor root))).1).lease := hcopy
      _ = resetClockWaitLease (C root).lease.val := hrow.2
  exact ⟨hmodeProjection.trans hrow.1, hlease⟩

/-- The incoming root service is also exactly one WAIT tick,
provided its OLD PACK pair is role-good. The latter is forced
by no defect entry on the incoming support edge. -/
theorem resetClockIncomingWaitPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hp : ResetTrialPhysical ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : GrantFree C root)
    (hw : ResetRootWaiting C root)
    (hpred : ring.rightNeighbor e = root)
    (hnoDef : ¬ ResetClockBankDefectEntry ring C root e) :
    (((protocol q).step ring C e) root).mode =
        resetClockWaitMode (C root).lease.val ∧
      (((protocol q).step ring C e) root).lease.val =
        resetClockWaitLease (C root).lease.val := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hgood :
      goodPair (compileAdvice q).b (C e).pack (C root).pack = true := by
    cases h : goodPair (compileAdvice q).b
        (C e).pack (C root).pack with
    | false =>
        exact False.elim
          (hnoDef ⟨Or.inl hpred, Or.inl (by rw [hpred]; exact h)⟩)
    | true =>
        rfl
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    have hh := congrArg Fin.val
      (roleUpdate_eq_self_of_good (compileAdvice q).b
        (C e).pack (C root).pack hgood)
    rw [roleUpdate_val] at hh
    exact hh.trans hroot
  have hx : (C e).pack.val ≠ 0 := by
    intro hz
    have hh :
        packNext (C e).pack.val (C root).pack.val
          (compileAdvice q).b = 1 := by
      rw [hz, hroot]
      simp [packNext, hb]
    omega
  have hrow :
      ((resetBankOld (C e) (C root)).2).mode =
        resetClockWaitMode (C root).lease.val ∧
      ((resetBankOld (C e) (C root)).2).lease =
        resetClockWaitLease (C root).lease.val := by
    have hh := resetClockIncomingWaitSymbolic
      (bankCell (C e) (C e).pack.val)
      (bankCell (C root) (C root).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C e).pack.val ≠ 0; exact hx)
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C root).grant = false; exact hg)
      (by change (C root).mode = .RWAIT; exact hw.1)
    simpa only [resetBankOld, hpost, bankCell] using hh
  have hn : 2 ≤ n := resetTrialMinRing ring C root hc hp
  have hmodeProjection := congrArg
    (fun z : Mode × Bool × BTok => z.1)
    ((resetPhysicalEdgeBankTrip ring C e
      (resetRootPortDistinct ring e hn) hsp).2)
  change (((protocol q).step ring C e)
    (ring.rightNeighbor e)).mode =
    ((resetBankOld (C e)
      (C (ring.rightNeighbor e))).2).mode at hmodeProjection
  rw [hpred] at hmodeProjection
  have hleaseProjection :=
    (resetClockPhysicalEdgeLeasePair ring C e
      (resetRootPortDistinct ring e hn) hsp).2
  rw [hpred] at hleaseProjection
  have hbound :
      ((resetBankOld (C e) (C root)).2).lease <
        (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2]
    exact resetClockWaitLeaseFits (C root)
  have hcopy :=
    resetClockCopyBankLeaseExact (C root)
      ((resetBankOld (C e) (C root)).2) hbound
  have hlease :
      (((protocol q).step ring C e) root).lease.val =
        resetClockWaitLease (C root).lease.val := by
    calc
      (((protocol q).step ring C e) root).lease.val =
          (copyBank (C root)
            ((resetBankOld (C e) (C root)).2)).lease.val :=
        congrArg Fin.val hleaseProjection
      _ = ((resetBankOld (C e) (C root)).2).lease := hcopy
      _ = resetClockWaitLease (C root).lease.val := hrow.2
  exact ⟨hmodeProjection.trans hrow.1, hlease⟩

/-- At an authenticated preterminal front the first digit is
E or RR, except in the physically returning-at-one stage. -/
theorem resetClockFirstDigitNonfinal {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hnonfinal : s ≠ .returning 1) :
    (C (site ring root 1)).tok = .E ∨
      (C (site ring root 1)).tok = .RR := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      by_cases hj : j = 1
      · subst j
        exact Or.inr hs.2.1.1.2.2
      · have hjgt : 1 < j := by
          have hp := hs.2.1.1.1
          omega
        exact Or.inl (hs.2.1.2 1 (by omega) hjgt).2
  | returning j =>
      by_cases hj : j = 1
      · subst j
        exact False.elim (hnonfinal rfl)
      · have hb : 1 ≤ (compileAdvice q).b :=
          Nat.le_trans hs.2.1.1 hs.2.1.2.1
        exact Or.inl
          (hs.2.2.2 1 (by omega) hb (by omega)).2

/-- When the root starts waiting with a positive lease, loss of
RWAIT on a role-good, grant-free, nonterminal selected step occurs
if and only if it services a root-incident edge with old lease one.
No exterior defect is silently counted as timeout. -/
theorem resetClockWaitLossIffLeaseExhaustion {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hnoDef : ¬ ResetClockBankDefectEntry ring C root e)
    (hnonfinal : ¬ (e = root ∧ s = .returning 1)) :
    ¬ ResetRootWaiting ((protocol q).step ring C e) root ↔
      (e = root ∨ ring.rightNeighbor e = root) ∧
        (C root).lease.val = 1 := by
  have hp : ResetTrialPhysical ring C root :=
    resetClockStageToTrial ring C root s hs
  have hw : ResetRootWaiting C root := by
    cases s with
    | finished =>
        cases hs
    | outward j =>
        exact hs.1
    | returning j =>
        exact hs.1
  have hpos : 0 < (C root).lease.val := hw.2
  by_cases he : e = root
  · subst e
    have hnotstage : s ≠ .returning 1 := by
      intro hfinal
      exact hnonfinal ⟨rfl, hfinal⟩
    have htok := resetClockFirstDigitNonfinal
      ring C root s hs hnotstage
    have hfields := resetClockOutgoingWaitPhysical
      ring C root hc hp hsp hg hw htok
    have hiff := resetClockWaitFieldsIff C
      ((protocol q).step ring C root) root hfields.1 hfields.2
    constructor
    · intro hbad
      have hnolease : ¬ 1 < (C root).lease.val := by
        intro hlong
        exact hbad (hiff.mpr hlong)
      exact ⟨Or.inl rfl, by omega⟩
    · intro hpair hwait
      have hlong := hiff.mp hwait
      omega
  · by_cases hpred : ring.rightNeighbor e = root
    · have hfields := resetClockIncomingWaitPhysical
        ring C root e hc hp hsp hg hw hpred hnoDef
      have hiff := resetClockWaitFieldsIff C
        ((protocol q).step ring C e) root hfields.1 hfields.2
      constructor
      · intro hbad
        have hnolease : ¬ 1 < (C root).lease.val := by
          intro hlong
          exact hbad (hiff.mpr hlong)
        exact ⟨Or.inr hpred, by omega⟩
      · intro hpair hwait
        have hlong := hiff.mp hwait
        omega
    · have hframe := step_frame ring C e root
        (Ne.symm he) (Ne.symm hpred)
      have hstill :
          ResetRootWaiting ((protocol q).step ring C e) root := by
        unfold ResetRootWaiting at hw ⊢
        rw [hframe]
        exact hw
      constructor
      · intro hbad
        exact False.elim (hbad hstill)
      · intro hbad
        rcases hbad.1 with hz | hy
        · exact False.elim (he hz)
        · exact False.elim (hpred hy)

/-- Exact classification of the existing comparison's waitLoss exit:
outside the success/defect/grant branches, it is precisely physical
lease exhaustion on one of the root's two incident services. -/
theorem resetClockBankOutcomeWaitLossIff {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hnoDef : ¬ ResetClockBankDefectEntry ring C root e)
    (hnonfinal : ¬ (e = root ∧ s = .returning 1))
    (hgnew : GrantFree ((protocol q).step ring C e) root) :
    resetClockBankOutcome ring root C s e = .waitLoss ↔
      (e = root ∨ ring.rightNeighbor e = root) ∧
        (C root).lease.val = 1 := by
  have hlease := resetClockWaitLossIffLeaseExhaustion
    ring C root e hsp hc hg s hs hnoDef hnonfinal
  simpa [resetClockBankOutcome, hnoDef, hnonfinal, hgnew] using hlease

end Counter
end L3


/-!
Finite-horizon BANK comparison failure numerator.

This block supplies the exact failure-count recursion for the
actual resetClockBankComparisonNext, treating only waitLoss as a
failure. Its combinatorial induction turns an explicitly stated
one-step superharmonic inequality into a finite-horizon bound.

The intended C.1 race weight is also defined. Its missing
superharmonic-drift inequality is NOT introduced as an invented premise or
claimed as a theorem. Thus neither the quantitative C.1 bound
nor the retry-kernel C.2 renewal is asserted here.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Number of uniform length-T scheduler words whose absorbing
comparison outcome is waitLoss. Success, defect and grant exits
contribute zero. In a waitLoss state every remaining edge word
is counted because that outcome is absorbing. -/
noncomputable def resetClockBankFailureCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankComparisonState q n → Nat → Nat
  | x, 0 => if x.2 = .waitLoss then 1 else 0
  | x, T + 1 =>
      if x.2 = .live then
        (List.ofFn (fun e : Fin n =>
          resetClockBankFailureCount ring root
            (resetClockBankComparisonNext ring root x e) T)).sum
      else if x.2 = .waitLoss then n ^ (T + 1) else 0

/-- Failure is an absorbing cylinder event: every continuation
of a recorded waitLoss contributes one scheduler word. -/
theorem resetClockBankFailureCountWaitLoss {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hw : x.2 = .waitLoss) (T : Nat) :
    resetClockBankFailureCount ring root x T = n ^ T := by
  cases T with
  | zero =>
      simp [resetClockBankFailureCount, hw]
  | succ T =>
      simp [resetClockBankFailureCount, hw]

/-- All other absorbing outcomes contribute no failure mass.
In particular an incoming role defect is not charged to C.1. -/
theorem resetClockBankFailureCountOtherExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hl : x.2 ≠ .live)
    (hw : x.2 ≠ .waitLoss) (T : Nat) :
    resetClockBankFailureCount ring root x T = 0 := by
  cases T with
  | zero =>
      simp [resetClockBankFailureCount, hw]
  | succ T =>
      simp [resetClockBankFailureCount, hl, hw]

/-- Exact one-edge numerator. Its right side is the uniform-IID
count of all scheduler edges that first enter waitLoss, rather
than success, defect or grant. -/
theorem resetClockBankFailureCountOne {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hl : x.2 = .live) :
    resetClockBankFailureCount ring root x 1 =
      (List.ofFn (fun e : Fin n =>
        if (resetClockBankComparisonNext ring root x e).2 =
            .waitLoss then 1 else 0)).sum := by
  simp [resetClockBankFailureCount, hl]

/-- The failure numerator is always at most the number n^T
of all length-T edge words, without any physical assumptions.
This is a first genuine stopping-tree mass certificate, though
not yet the exponentially small C.1 bound. -/
theorem resetClockBankFailureCountLeWords {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (x : ResetClockBankComparisonState q n) (T : Nat),
      resetClockBankFailureCount ring root x T ≤ n ^ T := by
  intro x T
  induction T generalizing x with
  | zero =>
      by_cases hw : x.2 = .waitLoss
      · simp [resetClockBankFailureCount, hw]
      · simp [resetClockBankFailureCount, hw]
  | succ T ih =>
      by_cases hl : x.2 = .live
      · have hh := ofFn_sum_le
          (fun e : Fin n =>
            resetClockBankFailureCount ring root
              (resetClockBankComparisonNext ring root x e) T)
          (fun _ : Fin n => n ^ T)
          (fun e => ih (resetClockBankComparisonNext ring root x e))
        calc
          resetClockBankFailureCount ring root x (T + 1) =
              (List.ofFn (fun e : Fin n =>
                resetClockBankFailureCount ring root
                  (resetClockBankComparisonNext ring root x e) T)).sum := by
                simp [resetClockBankFailureCount, hl]
          _ ≤ (List.ofFn (fun _ : Fin n => n ^ T)).sum := hh
          _ = n * n ^ T := ofFn_sum_const n (n ^ T)
          _ = n ^ (T + 1) := by rw [Nat.pow_succ]; ac_rfl
      · by_cases hw : x.2 = .waitLoss
        · simp [resetClockBankFailureCount, hl, hw]
        · simp [resetClockBankFailureCount, hl, hw]

/-- Distinct PACK values ensure a strictly interior digit edge
is neither the outgoing nor the incoming edge of the root. -/
theorem resetClockInteriorEdgeNotRootIncident {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j + 1 ≤ (compileAdvice q).b) :
    site ring root j ≠ root ∧
      ring.rightNeighbor (site ring root j) ≠ root := by
  have hx : site ring root j ≠ root := by
    change site ring root j ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      j 0 (by omega) (by omega) (by omega)
  have hy : site ring root (j + 1) ≠ root := by
    change site ring root (j + 1) ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      (j + 1) 0 hjb (by omega) (by omega)
  exact ⟨hx, by
    change site ring root (j + 1) ≠ root
    exact hy⟩

/-- Except at the final RETURN(1), the nominated productive
edge cannot touch the root at either endpoint. Thus there is
NO overlap between a productive service and either root-incident
unproductive lease tick at any other authenticated stage. -/
theorem resetClockNominatedNotRootIncident {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hfinal : s ≠ .returning 1) :
    resetClockNominated ring root (compileAdvice q).b s ≠ root ∧
      ring.rightNeighbor
        (resetClockNominated ring root (compileAdvice q).b s) ≠ root := by
  cases s with
  | finished =>
      cases hs
  | outward j =>
      have hjpos : 1 ≤ j := hs.2.1.1.1
      have hjbound : j ≤ (compileAdvice q).b := hs.2.1.1.2.1
      by_cases hjlt : j < (compileAdvice q).b
      · have hh := resetClockInteriorEdgeNotRootIncident
          ring C root hc j hjpos (by omega)
        simpa [resetClockNominated, hjlt] using hh
      · have hjtop : j = (compileAdvice q).b := by omega
        have hb : 2 ≤ (compileAdvice q).b := by
          have hh := resetTrialCompiledWidth q
          omega
        have hh := resetClockInteriorEdgeNotRootIncident
          ring C root hc ((compileAdvice q).b - 1)
          (by omega) (by omega)
        rw [hjtop]
        simpa [resetClockNominated] using hh
  | returning j =>
      by_cases hjone : j = 1
      · subst j
        exact False.elim (hfinal rfl)
      · have hjpos : 1 ≤ j := hs.2.1.1
        have hjbound : j ≤ (compileAdvice q).b := hs.2.1.2.1
        have hjgt : 1 < j := by omega
        have hh := resetClockInteriorEdgeNotRootIncident
          ring C root hc (j - 1) (by omega) (by omega)
        simpa [resetClockNominated, hjgt] using hh

/-- At an authenticated preterminal stage, the abstract clock
rank decreases by exactly one on the nominated edge, and is
unchanged on every other edge. This holds for the actual
comparison's ghost transition, not a replacement front clock. -/
theorem resetClockBankRankStepExact {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n) :
    resetClockRank (compileAdvice q).b
        (resetClockNext ring root (compileAdvice q).b s e) +
      (if e = resetClockNominated ring root (compileAdvice q).b s
        then 1 else 0) =
      resetClockRank (compileAdvice q).b s := by
  have hnt : ¬ resetClockTerminal (compileAdvice q).b s :=
    resetClockStageAtNotTerminal ring C root s hs
  have hb : 2 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hh := resetClockStepBalance ring root
    (compileAdvice q).b hb s e
  simpa [hnt] using hh

/-- The finite-horizon proof can be made entirely in Nat.
Its only analytic input is an explicit one-step weighted drift:
the sum of successor weights does not exceed n times the
current weight. Theorem does not assert that any particular
physical BANK comparison satisfies that drift. -/
theorem resetClockBankFailureCountWeighted
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (W : ResetClockBankComparisonState q n → Nat)
    (scale : Nat)
    (Good : ResetClockBankComparisonState q n → Prop)
    (hclosed : ∀ x e, Good x →
      Good (resetClockBankComparisonNext ring root x e))
    (hfail : ∀ x, x.2 = .waitLoss → scale ≤ W x)
    (hdrift : ∀ x, Good x → x.2 = .live →
      (List.ofFn (fun e : Fin n =>
        W (resetClockBankComparisonNext ring root x e))).sum ≤
          n * W x) :
    ∀ x, Good x → ∀ T,
      scale * resetClockBankFailureCount ring root x T ≤
        n ^ T * W x := by
  intro x hx T
  induction T generalizing x with
  | zero =>
      by_cases hw : x.2 = .waitLoss
      · simpa [resetClockBankFailureCount, hw] using hfail x hw
      · simp [resetClockBankFailureCount, hw]
  | succ T ih =>
      by_cases hl : x.2 = .live
      · have hchild : ∀ e : Fin n,
            scale * resetClockBankFailureCount ring root
              (resetClockBankComparisonNext ring root x e) T ≤
            n ^ T * W (resetClockBankComparisonNext ring root x e) := by
          intro e
          exact ih (resetClockBankComparisonNext ring root x e)
            (hclosed x e hx)
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            scale * resetClockBankFailureCount ring root
              (resetClockBankComparisonNext ring root x e) T)
          (fun e : Fin n =>
            n ^ T * W (resetClockBankComparisonNext ring root x e))
          hchild
        calc
          scale * resetClockBankFailureCount ring root x (T + 1) =
              (List.ofFn (fun e : Fin n =>
                scale * resetClockBankFailureCount ring root
                  (resetClockBankComparisonNext ring root x e) T)).sum := by
              rw [show resetClockBankFailureCount ring root x
                  (T + 1) =
                  (List.ofFn (fun e : Fin n =>
                    resetClockBankFailureCount ring root
                      (resetClockBankComparisonNext ring root x e) T)).sum
                from by simp [resetClockBankFailureCount, hl]]
              exact (ofFn_sum_mul_left scale _).symm
          _ ≤ (List.ofFn (fun e : Fin n =>
                n ^ T * W
                  (resetClockBankComparisonNext ring root x e))).sum :=
            hsum
          _ = n ^ T *
                (List.ofFn (fun e : Fin n =>
                  W (resetClockBankComparisonNext ring root x e))).sum :=
            ofFn_sum_mul_left (n ^ T) _
          _ ≤ n ^ T * (n * W x) :=
            Nat.mul_le_mul_left _ (hdrift x hx hl)
          _ = n ^ (T + 1) * W x := by
            rw [Nat.pow_succ]
            ac_rfl
      · by_cases hw : x.2 = .waitLoss
        · calc
            scale * resetClockBankFailureCount ring root x (T + 1) =
                scale * n ^ (T + 1) := by
              simp [resetClockBankFailureCount, hl, hw]
            _ ≤ W x * n ^ (T + 1) :=
              Nat.mul_le_mul_right _ (hfail x hw)
            _ = n ^ (T + 1) * W x := by
              ac_rfl
        · simp [resetClockBankFailureCount, hl, hw]

/-- Fixed integer denominator used to express the paper's
exponential-moment potential without Rational arithmetic.
L=2b+2, Lambda=13(b+2). -/
def resetClockBankRaceScale (q : Nat) : Nat :=
  2 ^ (2 * (compileAdvice q).b + 2) *
    5 ^ (compileAdvice q).bankLeaseCap

/-- The scaled supermartingale candidate on LIVE states:
  V(rank, lease)=(5/2)^rank (4/5)^lease.
The scale 2^L 5^Lambda makes V integral for all legal ranks
and leases. A waitLoss exit carries scale (indicator 1);
the other three absorbing exits carry zero. -/
noncomputable def resetClockBankRaceWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n) : Nat :=
  if x.2 = .live then
    5 ^ (resetClockRank (compileAdvice q).b x.1.2) *
      4 ^ ((x.1.1 root).lease.val) *
      2 ^ (2 * (compileAdvice q).b + 2 -
        resetClockRank (compileAdvice q).b x.1.2) *
      5 ^ ((compileAdvice q).bankLeaseCap -
        (x.1.1 root).lease.val)
  else if x.2 = .waitLoss then
    resetClockBankRaceScale q
  else 0

theorem resetClockBankRaceWeightAtFailure {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hw : x.2 = .waitLoss) :
    resetClockBankRaceWeight ring root x =
      resetClockBankRaceScale q := by
  simp [resetClockBankRaceWeight, hw]

theorem resetClockBankRaceWeightAtOtherExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hl : x.2 ≠ .live) (hw : x.2 ≠ .waitLoss) :
    resetClockBankRaceWeight ring root x = 0 := by
  simp [resetClockBankRaceWeight, hl, hw]

/-- Fully proved FINITE-horizon weighted failure-count induction
for the actual comparison transition. The single unproved
quantitative obligation is exposed in hdrift, not hidden
as an unstated assumption or a replacement scheduler. -/
theorem resetClockBankFailureCountOfRaceDrift
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hdrift :
      ∀ x : ResetClockBankComparisonState q n,
        ResetClockBankComparisonGood ring root x →
        x.2 = .live →
        (List.ofFn (fun e : Fin n =>
          resetClockBankRaceWeight ring root
            (resetClockBankComparisonNext ring root x e))).sum ≤
          n * resetClockBankRaceWeight ring root x) :
    ∀ x : ResetClockBankComparisonState q n,
      ResetClockBankComparisonGood ring root x →
      ∀ T,
        resetClockBankRaceScale q *
          resetClockBankFailureCount ring root x T ≤
        n ^ T * resetClockBankRaceWeight ring root x := by
  exact resetClockBankFailureCountWeighted ring root
    (resetClockBankRaceWeight ring root)
    (resetClockBankRaceScale q)
    (ResetClockBankComparisonGood ring root)
    (fun x e hx =>
      resetClockBankComparisonGoodStep ring root hsp x hx e)
    (fun x hx => by
      rw [resetClockBankRaceWeightAtFailure ring root x hx]
      exact Nat.le_refl _)
    hdrift

end Counter
end L3


/-!
Exact root-lease updates on LIVE transitions.

These lemmas explain precisely the physical quantities needed to
discharge the weighted Bellman drift. In particular an ordinary
nominated edge never spends a root lease unit; the only nominated
root incident service is the already classified terminal success.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical

/-- A nominated preterminal productive hit other than final
RETURN(1) is fully framed at the root, including its BANK lease.
No independence or abstract replacement process is used. -/
theorem resetClockBankNominatedRootLeaseFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hfinal : s ≠ .returning 1) :
    (((protocol q).step ring C
        (resetClockNominated ring root (compileAdvice q).b s))
      root).lease = (C root).lease := by
  have hn := resetClockNominatedNotRootIncident
    ring C root hc s hs hfinal
  have hf := step_frame ring C
    (resetClockNominated ring root (compileAdvice q).b s)
    root (Ne.symm hn.1) (Ne.symm hn.2)
  exact congrArg (fun a : Agent (compileAdvice q) => a.lease) hf

/-- Every LIVE successor uses exactly one root-lease unit if
and only if its selected edge meets the root. All other services
leave that coordinate unchanged. In particular a successful
terminal root RL service cannot be a LIVE successor. -/
theorem resetClockBankLiveRootLeaseStep {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (e : Fin n)
    (hlive : resetClockBankOutcome ring root C s e = .live) :
    (((protocol q).step ring C e) root).lease.val =
      (if e = root ∨ ring.rightNeighbor e = root
        then (C root).lease.val - 1
        else (C root).lease.val) := by
  have hp : ResetTrialPhysical ring C root :=
    resetClockStageToTrial ring C root s hs
  have hw : ResetRootWaiting C root := by
    cases s with
    | finished =>
        cases hs
    | outward j =>
        exact hs.1
    | returning j =>
        exact hs.1
  have ha : ResetTrialAllowed ring root C e :=
    (resetClockBankOutcomeLiveAllowed
      ring C root hsp hc hg s hs e hlive).1
  have hnoDef : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hd
    have hdef : resetClockBankOutcome ring root C s e =
        .defect := by
      simp [resetClockBankOutcome, hd]
    rw [hdef] at hlive
    cases hlive
  by_cases he : e = root
  · subst e
    have hsne : s ≠ .returning 1 := by
      intro hfinal
      have hret : ResetReturnPhysical ring C root 1 := by
        rw [hfinal] at hs
        exact hs
      exact (resetTrialRootRlTerminalExcluded
        ring C root hc hsp hret) ha
    have htok := resetClockFirstDigitNonfinal
      ring C root s hs hsne
    have hfields := resetClockOutgoingWaitPhysical
      ring C root hc hp hsp hg hw htok
    have hlong : 1 < (C root).lease.val :=
      (resetClockWaitFieldsIff C
        ((protocol q).step ring C root) root
        hfields.1 hfields.2).1 ha.2.2.2
    have hlease :
        (((protocol q).step ring C root) root).lease.val =
          (C root).lease.val - 1 := by
      rw [hfields.2]
      simp [resetClockWaitLease, hlong]
    simpa using hlease
  · by_cases hpred : ring.rightNeighbor e = root
    · have hfields := resetClockIncomingWaitPhysical
        ring C root e hc hp hsp hg hw hpred hnoDef
      have hlong : 1 < (C root).lease.val :=
        (resetClockWaitFieldsIff C
          ((protocol q).step ring C e) root
          hfields.1 hfields.2).1 ha.2.2.2
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val - 1 := by
        rw [hfields.2]
        simp [resetClockWaitLease, hlong]
      simpa [he, hpred] using hlease
    · have hf := step_frame ring C e root
        (Ne.symm he) (Ne.symm hpred)
      have hlease :
          (((protocol q).step ring C e) root).lease.val =
            (C root).lease.val :=
        congrArg (fun a : Agent (compileAdvice q) => a.lease.val) hf
      simpa [he, hpred] using hlease

/-- On a LIVE comparison state the old root lease is positive,
and at most the compiled physical lease cap. This supplies
the natural-range side conditions for the race potential. -/
theorem resetClockBankLiveRootLeaseBounds {n q : Nat}
    (ring : DirectedRing n)
    (root : Fin n) (x : ResetClockBankComparisonState q n)
    (hg : ResetClockBankComparisonGood ring root x)
    (hlive : x.2 = .live) :
    0 < (x.1.1 root).lease.val ∧
      (x.1.1 root).lease.val ≤ (compileAdvice q).bankLeaseCap := by
  have hs := (hg hlive).2.2
  have hw : ResetRootWaiting x.1.1 root := by
    cases hphase : x.1.2 with
    | finished =>
        rw [hphase] at hs
        cases hs
    | outward j =>
        rw [hphase] at hs
        exact hs.1
    | returning j =>
        rw [hphase] at hs
        exact hs.1
  exact ⟨hw.2, by
    have hh := (x.1.1 root).lease.isLt
    omega⟩

/-- A LIVE physical stage has rank at least one, and no larger
than the conservative service budget L=2b+2. -/
theorem resetClockBankLiveRankBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hg : ResetClockBankComparisonGood ring root x)
    (hlive : x.2 = .live) :
    1 ≤ resetClockRank (compileAdvice q).b x.1.2 ∧
      resetClockRank (compileAdvice q).b x.1.2 ≤
        2 * (compileAdvice q).b + 2 := by
  have hs := (hg hlive).2.2
  have hb : 2 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  cases hphase : x.1.2 with
  | finished =>
      rw [hphase] at hs
      cases hs
  | outward j =>
      rw [hphase] at hs
      have hjpos : 1 ≤ j := hs.2.1.1.1
      have hjbound : j ≤ (compileAdvice q).b :=
        hs.2.1.1.2.1
      simp only [hphase, resetClockRank]
      omega
  | returning j =>
      rw [hphase] at hs
      have hjpos : 1 ≤ j := hs.2.1.1
      have hjbound : j ≤ (compileAdvice q).b :=
        hs.2.1.2.1
      simp only [hphase, resetClockRank]
      omega

end Counter
end L3


/-!
Exact FiniteUniformStoppingTree interface.

The custom BANK comparison failure numerator is identified with the
ordinary stopped-tree failureCount. The tree marks
waitLoss as failure, and all success, grant and defect exits as
nonfailure terminal outcomes.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- Convert the existing comparison state to a standard two-outcome
stopping-tree node. Defect and grant are nonfailure terminations. -/
noncomputable def resetClockBankTreeNode {n q : Nat}
    (x : ResetClockBankComparisonState q n) :
    StopNode (ResetClockBankComparisonState q n) :=
  if x.2 = .live then .active x
  else if x.2 = .waitLoss then .failure
  else .success

/-- Exact tree step: first advance the genuine physical comparison
and only then classify its absorbing outcome. -/
noncomputable def resetClockBankTreeStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n) (e : Fin n) :
    StopNode (ResetClockBankComparisonState q n) :=
  resetClockBankTreeNode
    (resetClockBankComparisonNext ring root x e)

/-- The standard tree's failure leaf stays a failure under every
remaining scheduler edge word. -/
theorem resetClockBankTreeFailureFull {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ T,
      failureCount (resetClockBankTreeStep ring root)
        (.failure : StopNode (ResetClockBankComparisonState q n)) T =
      n ^ T := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount (resetClockBankTreeStep ring root)
            (.failure : StopNode (ResetClockBankComparisonState q n)) T)).sum =
        n ^ (T + 1)
      calc
        (List.ofFn (fun _ : Fin n =>
          failureCount (resetClockBankTreeStep ring root)
            (.failure : StopNode (ResetClockBankComparisonState q n)) T)).sum =
          (List.ofFn (fun _ : Fin n => n ^ T)).sum := by
            exact ofFn_sum_eq _ _ (fun _ => ih)
        _ = n * n ^ T := ofFn_sum_const n _
        _ = n ^ (T + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- A grant/defect/success terminal leaf contributes zero mass
to the watchdog-failure event, at every finite horizon. -/
theorem resetClockBankTreeSuccessZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ T,
      failureCount (resetClockBankTreeStep ring root)
        (.success : StopNode (ResetClockBankComparisonState q n)) T =
      0 := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount (resetClockBankTreeStep ring root)
            (.success : StopNode (ResetClockBankComparisonState q n)) T)).sum =
        0
      calc
        (List.ofFn (fun _ : Fin n =>
          failureCount (resetClockBankTreeStep ring root)
            (.success : StopNode (ResetClockBankComparisonState q n)) T)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum := by
            exact ofFn_sum_eq _ _ (fun _ => ih)
        _ = 0 := by rw [ofFn_sum_const]; omega

/-- Pointwise agreement between the custom exact recursion and the
standard FiniteUniformStoppingTree failure mass. -/
theorem resetClockBankFailureCountEqTree {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (x : ResetClockBankComparisonState q n) (T : Nat),
      resetClockBankFailureCount ring root x T =
        failureCount (resetClockBankTreeStep ring root)
          (resetClockBankTreeNode x) T := by
  intro x T
  induction T generalizing x with
  | zero =>
      by_cases hl : x.2 = .live
      · have hw : x.2 ≠ .waitLoss := by
          intro h
          rw [hl] at h
          cases h
        simp [resetClockBankFailureCount,
          resetClockBankTreeNode, hl, hw,
          failureCount, treeWeight, failureWeight]
      · by_cases hw : x.2 = .waitLoss
        · simp [resetClockBankFailureCount,
            resetClockBankTreeNode, hl, hw,
            failureCount, treeWeight, failureWeight]
        · simp [resetClockBankFailureCount,
            resetClockBankTreeNode, hl, hw,
            failureCount, treeWeight, failureWeight]
  | succ T ih =>
      by_cases hl : x.2 = .live
      · have hnode : resetClockBankTreeNode x = .active x := by
          simp [resetClockBankTreeNode, hl]
        rw [hnode]
        change
          resetClockBankFailureCount ring root x (T + 1) =
            (List.ofFn (fun e : Fin n =>
              failureCount (resetClockBankTreeStep ring root)
                (resetClockBankTreeNode
                  (resetClockBankComparisonNext ring root x e)) T)).sum
        rw [show resetClockBankFailureCount ring root x (T + 1) =
            (List.ofFn (fun e : Fin n =>
              resetClockBankFailureCount ring root
                (resetClockBankComparisonNext ring root x e) T)).sum
          from by simp [resetClockBankFailureCount, hl]]
        exact ofFn_sum_eq _ _ (fun e =>
          ih (resetClockBankComparisonNext ring root x e))
      · by_cases hw : x.2 = .waitLoss
        · have hnode : resetClockBankTreeNode x = .failure := by
            simp [resetClockBankTreeNode, hl, hw]
          rw [hnode]
          calc
            resetClockBankFailureCount ring root x (T + 1) =
                n ^ (T + 1) :=
              resetClockBankFailureCountWaitLoss ring root x hw (T + 1)
            _ = failureCount (resetClockBankTreeStep ring root)
                  (.failure : StopNode (ResetClockBankComparisonState q n))
                  (T + 1) :=
              (resetClockBankTreeFailureFull ring root (T + 1)).symm
        · have hnode : resetClockBankTreeNode x = .success := by
            simp [resetClockBankTreeNode, hl, hw]
          rw [hnode]
          calc
            resetClockBankFailureCount ring root x (T + 1) = 0 :=
              resetClockBankFailureCountOtherExit ring root x hl hw (T + 1)
            _ = failureCount (resetClockBankTreeStep ring root)
                  (.success : StopNode (ResetClockBankComparisonState q n))
                  (T + 1) :=
              (resetClockBankTreeSuccessZero ring root (T + 1)).symm

/-- The finite-horizon weighted inequality is therefore literally
a stopping-tree failure-mass bound, with the remaining local drift
hypothesis stated explicitly. -/
theorem resetClockBankTreeFailureOfRaceDrift
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hdrift :
      ∀ x : ResetClockBankComparisonState q n,
        ResetClockBankComparisonGood ring root x →
        x.2 = .live →
        (List.ofFn (fun e : Fin n =>
          resetClockBankRaceWeight ring root
            (resetClockBankComparisonNext ring root x e))).sum ≤
          n * resetClockBankRaceWeight ring root x) :
    ∀ x : ResetClockBankComparisonState q n,
      ResetClockBankComparisonGood ring root x →
      ∀ T,
        resetClockBankRaceScale q *
          failureCount (resetClockBankTreeStep ring root)
            (resetClockBankTreeNode x) T ≤
        n ^ T * resetClockBankRaceWeight ring root x := by
  intro x hx T
  rw [← resetClockBankFailureCountEqTree ring root x T]
  exact resetClockBankFailureCountOfRaceDrift
    ring root hsp hdrift x hx T

end Counter
end L3


/-!
Local race arithmetic and finite uniform three-edge drift.

The numerical identities are over
abstract natural parameters, avoiding nonlinear literal expansion.
No unproved global drift is declared.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- Pure-natural live weight from the earlier BANK race potential,
with abstract rank budget L and lease cap cap. -/
def resetClockRawRaceWeight
    (L cap rank lease : Nat) : Nat :=
  5 ^ rank * 4 ^ lease * 2 ^ (L - rank) * 5 ^ (cap - lease)

/-- Productive service: dropping rank by one multiplies the
weight by exactly 2/5, provided rank is in range. -/
theorem resetClockRawRankDrop
    (L cap rank lease : Nat)
    (hr : 1 ≤ rank) (hL : rank ≤ L) :
    5 * resetClockRawRaceWeight L cap (rank - 1) lease =
      2 * resetClockRawRaceWeight L cap rank lease := by
  have hpRank : 5 ^ rank = 5 ^ (rank - 1) * 5 := by
    have h : rank - 1 + 1 = rank := by omega
    calc
      5 ^ rank = 5 ^ (rank - 1 + 1) := by rw [h]
      _ = 5 ^ (rank - 1) * 5 := by rw [Nat.pow_succ]
  have hpLeft :
      2 ^ (L - (rank - 1)) = 2 ^ (L - rank) * 2 := by
    have h : L - (rank - 1) = (L - rank) + 1 := by omega
    rw [h, Nat.pow_succ]
  unfold resetClockRawRaceWeight
  rw [hpLeft, hpRank]
  ac_rfl

/-- One unproductive root incident: decrementing a positive
lease multiplies the weight by exactly 5/4. -/
theorem resetClockRawLeaseDrop
    (L cap rank lease : Nat)
    (hl : 1 ≤ lease) (hcap : lease ≤ cap) :
    4 * resetClockRawRaceWeight L cap rank (lease - 1) =
      5 * resetClockRawRaceWeight L cap rank lease := by
  have hpLease : 4 ^ lease = 4 ^ (lease - 1) * 4 := by
    have h : lease - 1 + 1 = lease := by omega
    calc
      4 ^ lease = 4 ^ (lease - 1 + 1) := by rw [h]
      _ = 4 ^ (lease - 1) * 4 := by rw [Nat.pow_succ]
  have hpCap :
      5 ^ (cap - (lease - 1)) = 5 ^ (cap - lease) * 5 := by
    have h : cap - (lease - 1) = (cap - lease) + 1 := by
      omega
    rw [h, Nat.pow_succ]
  unfold resetClockRawRaceWeight
  rw [hpLease, hpCap]
  ac_rfl

/-- On a lease-one exit, the absorbing failure indicator has
weight at most 5/4 times the old live race weight. -/
theorem resetClockRawTimeoutBound
    (L cap rank : Nat) (hL : rank ≤ L)
    (hcap : 1 ≤ cap) :
    4 * (2 ^ L * 5 ^ cap) ≤
      5 * resetClockRawRaceWeight L cap rank 1 := by
  have hp : 2 ^ rank ≤ 5 ^ rank :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 5) rank
  have hpowL : 2 ^ L = 2 ^ rank * 2 ^ (L - rank) := by
    have h : rank + (L - rank) = L := by omega
    calc
      2 ^ L = 2 ^ (rank + (L - rank)) := by rw [h]
      _ = 2 ^ rank * 2 ^ (L - rank) := by rw [Nat.pow_add]
  have hpowCap :
      5 ^ cap = 5 ^ (cap - 1) * 5 := by
    have h : cap - 1 + 1 = cap := by omega
    calc
      5 ^ cap = 5 ^ (cap - 1 + 1) := by rw [h]
      _ = 5 ^ (cap - 1) * 5 := by rw [Nat.pow_succ]
  have hm := Nat.mul_le_mul_left
    (4 * 2 ^ (L - rank) * 5 ^ (cap - 1) * 5) hp
  calc
    4 * (2 ^ L * 5 ^ cap) =
        (4 * 2 ^ (L - rank) * 5 ^ (cap - 1) * 5) *
          2 ^ rank := by rw [hpowL, hpowCap]; ac_rfl
    _ ≤ (4 * 2 ^ (L - rank) * 5 ^ (cap - 1) * 5) *
          5 ^ rank := hm
    _ = 5 * resetClockRawRaceWeight L cap rank 1 := by
      simp only [resetClockRawRaceWeight, Nat.pow_one]
      ac_rfl

/-- A single exceptional index in a finite uniform scheduler sum.
Copied into the current namespace because the analogous Prob lemma
is private to its own source file. -/
theorem resetClockOfFnSpike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n =>
        if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh :=
            ofFn_sum_eq
              (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1)) then v else 0)
              (fun _ : Fin n => 0)
              (by
                intro i
                have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                  intro he
                  have hv := congrArg Fin.val he
                  change i.val + 1 = 0 at hv
                  omega
                rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh :=
          ofFn_sum_eq
            (fun i : Fin n => if i.succ = a.succ then v else 0)
            (fun i : Fin n => if i = a then v else 0)
            (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- At most one scheduler edge can have the given root as
responder: rightNeighbor is injective. No leftNeighbor formula,
modular arithmetic, or additional ring-size premise is required. -/
theorem resetClockIncomingSpikeLe {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if ring.rightNeighbor e = root then v else 0)).sum ≤ v := by
  by_cases hw : ∃ a : Fin n, ring.rightNeighbor a = root
  · obtain ⟨a, ha⟩ := hw
    have hpoint : ∀ e : Fin n,
        (if ring.rightNeighbor e = root then v else 0) =
          (if e = a then v else 0) := by
      intro e
      by_cases he : e = a
      · subst e
        simp [ha]
      · have hn : ring.rightNeighbor e ≠ root := by
          intro h
          exact he (resetTrialNeighborInjective ring (h.trans ha.symm))
        simp [he, hn]
    calc
      (List.ofFn (fun e : Fin n =>
        if ring.rightNeighbor e = root then v else 0)).sum =
          (List.ofFn (fun e : Fin n =>
            if e = a then v else 0)).sum :=
        ofFn_sum_eq _ _ hpoint
      _ = v := resetClockOfFnSpike n a v
      _ ≤ v := Nat.le_refl _
  · have hpoint : ∀ e : Fin n,
        (if ring.rightNeighbor e = root then v else 0) = 0 := by
      intro e
      have hn : ring.rightNeighbor e ≠ root := by
        intro he
        exact hw ⟨e, he⟩
      simp [hn]
    calc
      (List.ofFn (fun e : Fin n =>
        if ring.rightNeighbor e = root then v else 0)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum :=
        ofFn_sum_eq _ _ hpoint
      _ = 0 := by rw [ofFn_sum_const]; omega
      _ ≤ v := Nat.zero_le _

/-- Abstract three-edge drift. One nominated productive edge has
factor ≤ 2/5, outgoing and incoming root incidents factor ≤ 5/4,
and all other edges factor ≤ 1. The exceptional cases may even
overlap; this finite-sum theorem does not assume disjointness.
20 times the pointwise inequalities yield a 2W surplus. -/
theorem resetClockThreeEdgeDrift {n : Nat}
    (ring : DirectedRing n) (root nominated : Fin n)
    (W : Nat) (f : Fin n → Nat)
    (hprod : 5 * f nominated ≤ 2 * W)
    (hout : 4 * f root ≤ 5 * W)
    (hin : ∀ e : Fin n, ring.rightNeighbor e = root →
      4 * f e ≤ 5 * W)
    (hother : ∀ e : Fin n,
      e ≠ nominated → e ≠ root →
      ring.rightNeighbor e ≠ root → f e ≤ W) :
    (List.ofFn f).sum ≤ n * W := by
  have hpoint : ∀ e : Fin n,
      20 * f e + (if e = nominated then 12 * W else 0) ≤
        (20 * W + (if e = root then 5 * W else 0)) +
          (if ring.rightNeighbor e = root then 5 * W else 0) := by
    intro e
    by_cases he : e = nominated
    · have hh : 5 * f e ≤ 2 * W := by
        rw [he]
        exact hprod
      simp only [if_pos he]
      omega
    · by_cases hr : e = root
      · have hh : 4 * f e ≤ 5 * W := by
          rw [hr]
          exact hout
        simp only [if_neg he, if_pos hr]
        omega
      · by_cases hi : ring.rightNeighbor e = root
        · have hh : 4 * f e ≤ 5 * W := hin e hi
          simp only [if_neg he, if_neg hr, if_pos hi]
          omega
        · have hh : f e ≤ W := hother e he hr hi
          simp only [if_neg he, if_neg hr, if_neg hi]
          omega
  have hsum :=
    ofFn_sum_le
      (fun e : Fin n =>
        20 * f e + (if e = nominated then 12 * W else 0))
      (fun e : Fin n =>
        (20 * W + (if e = root then 5 * W else 0)) +
          (if ring.rightNeighbor e = root then 5 * W else 0))
      hpoint
  have hleft :
      (List.ofFn (fun e : Fin n =>
        20 * f e + (if e = nominated then 12 * W else 0))).sum =
          20 * (List.ofFn f).sum + 12 * W := by
    rw [ofFn_sum_add, ofFn_sum_mul_left]
    rw [resetClockOfFnSpike n nominated (12 * W)]
  have hright :
      (List.ofFn (fun e : Fin n =>
        (20 * W + (if e = root then 5 * W else 0)) +
          (if ring.rightNeighbor e = root then 5 * W else 0))).sum =
        20 * (n * W) + 5 * W +
          (List.ofFn (fun e : Fin n =>
            if ring.rightNeighbor e = root then 5 * W else 0)).sum := by
    rw [ofFn_sum_add, ofFn_sum_add,
      ofFn_sum_const, resetClockOfFnSpike n root (5 * W)]
    ac_rfl
  rw [hleft, hright] at hsum
  have hincoming :=
    resetClockIncomingSpikeLe ring root (5 * W)
  have hmain :
      20 * (List.ofFn f).sum ≤ 20 * (n * W) := by
    omega
  omega

end Counter
end L3


/-!
The ordinary-edge branch of the physical drift.

A selected edge that is neither nominated nor incident to the root
keeps the exact rank and full root Agent if the comparison stays
live. The only other outcome relevant to race weight is waitLoss;
that one is impossible away from the two root-incident edges.
All other exits have zero race weight.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- The earlier live race weight reads only stage rank and the
root lease, not the rest of the Cartesian physical state. -/
theorem resetClockLiveRaceWeightCongr {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x y : ResetClockBankComparisonState q n)
    (hx : x.2 = .live) (hy : y.2 = .live)
    (hr : resetClockRank (compileAdvice q).b x.1.2 =
      resetClockRank (compileAdvice q).b y.1.2)
    (hl : (x.1.1 root).lease.val =
      (y.1.1 root).lease.val) :
    resetClockBankRaceWeight ring root x =
      resetClockBankRaceWeight ring root y := by
  simp [resetClockBankRaceWeight, hx, hy, hr, hl]

/-- An actual waitLoss exit is necessarily at a root-incident edge.
This does not infer a timeout from an unrelated grant/defect exit. -/
theorem resetClockBankOutcomeWaitLossIncident {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hwait : resetClockBankOutcome ring root C s e = .waitLoss) :
    e = root ∨ ring.rightNeighbor e = root := by
  have hcases :=
    resetClockBankOutcomeCases ring C root hsp hc hg s hs e
  rcases hcases with hl | ⟨hd, _⟩ |
      ⟨hfinish, _, _, _, _⟩ | ⟨hgrant, _⟩ | ⟨hw, hlose⟩
  · rw [hwait] at hl
    cases hl
  · rw [hwait] at hd
    cases hd
  · rw [hwait] at hfinish
    cases hfinish
  · rw [hwait] at hgrant
    cases hgrant
  · exact resetClockBankWaitLossIncident
      ring C root e s hs hlose

/-- A comparison edge which terminates outside waitLoss has
zero failure potential, whether it exits in success, grant or
defect. This is a genuine projection onto comparisonNext. -/
theorem resetClockBankRaceOtherExitZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n) (e : Fin n)
    (hx : x.2 = .live)
    (hn : resetClockBankOutcome ring root x.1.1 x.1.2 e ≠ .live)
    (hw : resetClockBankOutcome ring root x.1.1 x.1.2 e ≠ .waitLoss) :
    resetClockBankRaceWeight ring root
      (resetClockBankComparisonNext ring root x e) = 0 := by
  have hclass :
      (resetClockBankComparisonNext ring root x e).2 =
        resetClockBankOutcome ring root x.1.1 x.1.2 e := by
    simp [resetClockBankComparisonNext, hx]
  have hl :
      (resetClockBankComparisonNext ring root x e).2 ≠ .live := by
    rw [hclass]
    exact hn
  have ht :
      (resetClockBankComparisonNext ring root x e).2 ≠ .waitLoss := by
    rw [hclass]
    exact hw
  exact resetClockBankRaceWeightAtOtherExit ring root
    (resetClockBankComparisonNext ring root x e) hl ht

/-- All ordinary, non-root-incident, non-nominated edges have
nonincreasing race weight on the ACTUAL comparison. -/
theorem resetClockBankRaceOrdinaryEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankComparisonState q n)
    (hg : ResetClockBankComparisonGood ring root x)
    (hl : x.2 = .live)
    (e : Fin n)
    (hnom : e ≠ resetClockNominated ring root
      (compileAdvice q).b x.1.2)
    (hroot : e ≠ root)
    (hpred : ring.rightNeighbor e ≠ root) :
    resetClockBankRaceWeight ring root
      (resetClockBankComparisonNext ring root x e) ≤
        resetClockBankRaceWeight ring root x := by
  obtain ⟨hc, hgrant, hs⟩ := hg hl
  by_cases hout :
      resetClockBankOutcome ring root x.1.1 x.1.2 e = .live
  · have hstep :
        resetClockBankComparisonNext ring root x e =
          (((protocol q).step ring x.1.1 e,
            resetClockNext ring root (compileAdvice q).b
              x.1.2 e), .live) := by
      simp [resetClockBankComparisonNext, hl, hout]
    have hrank :
        resetClockRank (compileAdvice q).b
          (resetClockNext ring root (compileAdvice q).b x.1.2 e) =
        resetClockRank (compileAdvice q).b x.1.2 := by
      have hh := resetClockBankRankStepExact
        ring x.1.1 root x.1.2 hs e
      rw [if_neg hnom] at hh
      omega
    have hframe :=
      step_frame ring x.1.1 e root
        (Ne.symm hroot) (Ne.symm hpred)
    have hchildLive :
        (resetClockBankComparisonNext ring root x e).2 = .live := by
      rw [hstep]
    have hchildRank :
        resetClockRank (compileAdvice q).b
          (resetClockBankComparisonNext ring root x e).1.2 =
        resetClockRank (compileAdvice q).b x.1.2 := by
      rw [hstep]
      exact hrank
    have hchildLease :
        ((resetClockBankComparisonNext ring root x e).1.1 root).lease.val =
          (x.1.1 root).lease.val := by
      rw [hstep]
      exact congrArg (fun a : Agent (compileAdvice q) => a.lease.val)
        hframe
    have heq := resetClockLiveRaceWeightCongr
      ring root (resetClockBankComparisonNext ring root x e) x
      hchildLive hl hchildRank hchildLease
    exact Nat.le_of_eq heq
  · have hnotwait :
        resetClockBankOutcome ring root x.1.1 x.1.2 e ≠
          .waitLoss := by
      intro hw
      have hi := resetClockBankOutcomeWaitLossIncident
        ring x.1.1 root e hsp hc hgrant x.1.2 hs hw
      rcases hi with he | hy
      · exact hroot he
      · exact hpred hy
    have hzero := resetClockBankRaceOtherExitZero
      ring root x e hl hout hnotwait
    rw [hzero]
    exact Nat.zero_le _

/-- The requested full drift follows from precisely three
local physical edge bounds; no fourth family of scheduler edges
is missing. This is a proved conditional *reduction*, not an
assertion that the three remaining bounds already hold. -/
theorem resetClockBankRaceDriftOfLocalBounds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hproductive :
      ∀ x : ResetClockBankComparisonState q n,
        ResetClockBankComparisonGood ring root x →
        x.2 = .live →
        5 * resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x
            (resetClockNominated ring root (compileAdvice q).b
              x.1.2)) ≤
          2 * resetClockBankRaceWeight ring root x)
    (houtgoing :
      ∀ x : ResetClockBankComparisonState q n,
        ResetClockBankComparisonGood ring root x →
        x.2 = .live →
        4 * resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x root) ≤
          5 * resetClockBankRaceWeight ring root x)
    (hincoming :
      ∀ x : ResetClockBankComparisonState q n,
        ResetClockBankComparisonGood ring root x →
        x.2 = .live →
        ∀ e : Fin n, ring.rightNeighbor e = root →
        4 * resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x e) ≤
          5 * resetClockBankRaceWeight ring root x) :
    ∀ x : ResetClockBankComparisonState q n,
      ResetClockBankComparisonGood ring root x →
      x.2 = .live →
      (List.ofFn (fun e : Fin n =>
        resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x e))).sum ≤
        n * resetClockBankRaceWeight ring root x := by
  intro x hx hl
  exact resetClockThreeEdgeDrift ring root
    (resetClockNominated ring root (compileAdvice q).b x.1.2)
    (resetClockBankRaceWeight ring root x)
    (fun e : Fin n =>
      resetClockBankRaceWeight ring root
        (resetClockBankComparisonNext ring root x e))
    (hproductive x hx hl)
    (houtgoing x hx hl)
    (hincoming x hx hl)
    (fun e hnom hroot hpred =>
      resetClockBankRaceOrdinaryEdge ring root hsp
        x hx hl e hnom hroot hpred)

end Counter
end L3


/-!
Nominated productive edge in the actual BANK comparison.

The only nominated edge touching the root is the final RETURN(1)
edge, whose comparison outcome is a success or defect, both
assigned zero race weight. Every other productive hit preserves
the root lease and decreases the exact abstract rank by one.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- In a LIVE state the old race weight is the abstract pure
natural product at the exact observed rank and root lease. -/
theorem resetClockRaceWeightLiveRaw {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankComparisonState q n)
    (hl : x.2 = .live) :
    resetClockBankRaceWeight ring root x =
      resetClockRawRaceWeight
        (2 * (compileAdvice q).b + 2)
        (compileAdvice q).bankLeaseCap
        (resetClockRank (compileAdvice q).b x.1.2)
        (x.1.1 root).lease.val := by
  simp [resetClockBankRaceWeight, resetClockRawRaceWeight, hl]

/-- A final physical RETURN(1) root service is classified before
the grant/timeout checks. Its comparison outcome is either defect
(if the boundary itself is bad) or success. -/
theorem resetClockBankFinalOutcomeTerminal {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (s : ResetClockStage)
    (hf : e = root ∧ s = .returning 1) :
    resetClockBankOutcome ring root C s e ≠ .live ∧
      resetClockBankOutcome ring root C s e ≠ .waitLoss := by
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · have heq : resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hd]
    constructor
    · rw [heq]
      decide
    · rw [heq]
      decide
  · have heq : resetClockBankOutcome ring root C s e = .success := by
      simp [resetClockBankOutcome, hd, hf,
        show ¬ ResetClockBankDefectEntry ring C root root from hf.1 ▸ hd]
    constructor
    · rw [heq]
      decide
    · rw [heq]
      decide

/-- The productive nominated edge has at most 2/5 of the old
race weight. This is an actual Protocol.step statement; it
handles the terminal RETURN(1) edge as a zero-weight exit. -/
theorem resetClockBankRaceProductiveEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankComparisonState q n)
    (hg : ResetClockBankComparisonGood ring root x)
    (hl : x.2 = .live) :
    5 * resetClockBankRaceWeight ring root
      (resetClockBankComparisonNext ring root x
        (resetClockNominated ring root (compileAdvice q).b
          x.1.2)) ≤
      2 * resetClockBankRaceWeight ring root x := by
  obtain ⟨hc, hgrant, hs⟩ := hg hl
  by_cases hfinal : x.1.2 = .returning 1
  · have hnom :
        resetClockNominated ring root (compileAdvice q).b x.1.2 =
          root := by
      simp [resetClockNominated, hfinal]
    have hstop := resetClockBankFinalOutcomeTerminal
      ring x.1.1 root
      (resetClockNominated ring root (compileAdvice q).b x.1.2)
      x.1.2 ⟨hnom, hfinal⟩
    have hz := resetClockBankRaceOtherExitZero ring root x
      (resetClockNominated ring root (compileAdvice q).b x.1.2)
      hl hstop.1 hstop.2
    rw [hz]
    exact Nat.zero_le _
  · have havoid := resetClockNominatedNotRootIncident
      ring x.1.1 root hc x.1.2 hs hfinal
    by_cases hout :
        resetClockBankOutcome ring root x.1.1 x.1.2
          (resetClockNominated ring root (compileAdvice q).b
            x.1.2) = .live
    · have hstep :
          resetClockBankComparisonNext ring root x
            (resetClockNominated ring root (compileAdvice q).b
              x.1.2) =
            (((protocol q).step ring x.1.1
                (resetClockNominated ring root (compileAdvice q).b
                  x.1.2),
              resetClockNext ring root (compileAdvice q).b
                x.1.2
                (resetClockNominated ring root (compileAdvice q).b
                  x.1.2)), .live) := by
        simp [resetClockBankComparisonNext, hl, hout]
      have hrank :
          resetClockRank (compileAdvice q).b
            (resetClockNext ring root (compileAdvice q).b
              x.1.2
              (resetClockNominated ring root (compileAdvice q).b
                x.1.2)) =
            resetClockRank (compileAdvice q).b x.1.2 - 1 := by
        have hh := resetClockBankRankStepExact
          ring x.1.1 root x.1.2 hs
          (resetClockNominated ring root (compileAdvice q).b
            x.1.2)
        rw [if_pos rfl] at hh
        omega
      have hlease := resetClockBankNominatedRootLeaseFrame
        ring x.1.1 root hc x.1.2 hs hfinal
      have hbefore := resetClockRaceWeightLiveRaw
        ring root x hl
      have hafter :
          resetClockBankRaceWeight ring root
            (resetClockBankComparisonNext ring root x
              (resetClockNominated ring root (compileAdvice q).b
                x.1.2)) =
          resetClockRawRaceWeight
            (2 * (compileAdvice q).b + 2)
            (compileAdvice q).bankLeaseCap
            (resetClockRank (compileAdvice q).b x.1.2 - 1)
            (x.1.1 root).lease.val := by
        rw [hstep]
        simp [resetClockBankRaceWeight, resetClockRawRaceWeight,
          hrank, hlease]
      have hbounds := resetClockBankLiveRankBounds ring root x hg hl
      have hratio := resetClockRawRankDrop
        (2 * (compileAdvice q).b + 2)
        (compileAdvice q).bankLeaseCap
        (resetClockRank (compileAdvice q).b x.1.2)
        (x.1.1 root).lease.val hbounds.1 hbounds.2
      rw [hafter, hbefore]
      exact Nat.le_of_eq hratio
    · have hnotwait :
          resetClockBankOutcome ring root x.1.1 x.1.2
            (resetClockNominated ring root (compileAdvice q).b
              x.1.2) ≠ .waitLoss := by
        intro hw
        have hi := resetClockBankOutcomeWaitLossIncident
          ring x.1.1 root
          (resetClockNominated ring root (compileAdvice q).b
            x.1.2) hsp hc hgrant x.1.2 hs hw
        rcases hi with hleft | hright
        · exact havoid.1 hleft
        · exact havoid.2 hright
      have hz := resetClockBankRaceOtherExitZero ring root x
        (resetClockNominated ring root (compileAdvice q).b
          x.1.2) hl hout hnotwait
      rw [hz]
      exact Nat.zero_le _

end Counter
end L3


/-!
Root-incident edge of the actual BANK race.

A live root incident is never the nominated productive edge.
If it stays live, rank is constant and the lease drops by one.
If it exits in waitLoss, the old lease is exactly one. All other
exits have zero race weight.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- A LIVE root incident is not nominated. The sole possible
overlap is RETURN(1) at the root, which is a terminal success
(or a defect) and therefore cannot remain LIVE. -/
theorem resetClockBankLiveIncidentNotNominated {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hinc : e = root ∨ ring.rightNeighbor e = root)
    (hlive : resetClockBankOutcome ring root C s e = .live) :
    e ≠ resetClockNominated ring root (compileAdvice q).b s := by
  by_cases hfinal : s = .returning 1
  · have hnom :
        resetClockNominated ring root (compileAdvice q).b s = root := by
      simp [resetClockNominated, hfinal]
    intro he
    have heq : e = root := he.trans hnom
    exact (resetClockBankFinalOutcomeTerminal
      ring C root e s ⟨heq, hfinal⟩).1 hlive
  · have hn := resetClockNominatedNotRootIncident
      ring C root hc s hs hfinal
    intro he
    rcases hinc with hr | hi
    · exact hn.1 (he.symm.trans hr)
    · exact hn.2 ((congrArg ring.rightNeighbor he.symm).trans hi)

/-- The physical waitLoss branch is necessarily exactly the
one-unit lease exhaustion on a root-incident edge. Defect,
terminal success, and new-grant outcomes have higher priority. -/
theorem resetClockBankWaitLossLeaseOne {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hwait : resetClockBankOutcome ring root C s e = .waitLoss) :
    (e = root ∨ ring.rightNeighbor e = root) ∧
      (C root).lease.val = 1 := by
  have hd : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hbad
    have heq : resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hbad]
    rw [heq] at hwait
    cases hwait
  have hf : ¬ (e = root ∧ s = .returning 1) := by
    intro hfinal
    exact (resetClockBankFinalOutcomeTerminal
      ring C root e s hfinal).2 hwait
  have hgnew : GrantFree ((protocol q).step ring C e) root := by
    by_cases hgr : GrantFree ((protocol q).step ring C e) root
    · exact hgr
    · have heq : resetClockBankOutcome ring root C s e = .grant := by
        simp [resetClockBankOutcome, hd, hf, hgr]
      rw [heq] at hwait
      cases hwait
  exact (resetClockBankOutcomeWaitLossIff
    ring C root e hsp hc hg s hs hd hf hgnew).1 hwait

/-- Root-incident physical service has race weight factor ≤5/4.
This covers outgoing, incoming, lease-one timeout, defect/grant
exits, and the final RETURN(1) success without treating any
exit as an invented physical transition. -/
theorem resetClockBankRaceIncidentEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankComparisonState q n)
    (hg : ResetClockBankComparisonGood ring root x)
    (hl : x.2 = .live)
    (e : Fin n)
    (hinc : e = root ∨ ring.rightNeighbor e = root) :
    4 * resetClockBankRaceWeight ring root
      (resetClockBankComparisonNext ring root x e) ≤
      5 * resetClockBankRaceWeight ring root x := by
  obtain ⟨hc, hgrant, hs⟩ := hg hl
  by_cases hout :
      resetClockBankOutcome ring root x.1.1 x.1.2 e = .live
  · have hnotnom := resetClockBankLiveIncidentNotNominated
      ring x.1.1 root e hc x.1.2 hs hinc hout
    have hstep :
        resetClockBankComparisonNext ring root x e =
          (((protocol q).step ring x.1.1 e,
            resetClockNext ring root (compileAdvice q).b
              x.1.2 e), .live) := by
      simp [resetClockBankComparisonNext, hl, hout]
    have hrank :
        resetClockRank (compileAdvice q).b
          (resetClockNext ring root (compileAdvice q).b
            x.1.2 e) =
        resetClockRank (compileAdvice q).b x.1.2 := by
      have hh := resetClockBankRankStepExact
        ring x.1.1 root x.1.2 hs e
      rw [if_neg hnotnom] at hh
      omega
    have hlease := resetClockBankLiveRootLeaseStep
      ring x.1.1 root hsp hc hgrant x.1.2 hs e hout
    rw [if_pos hinc] at hlease
    have hbefore := resetClockRaceWeightLiveRaw ring root x hl
    have hafter :
        resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x e) =
        resetClockRawRaceWeight
          (2 * (compileAdvice q).b + 2)
          (compileAdvice q).bankLeaseCap
          (resetClockRank (compileAdvice q).b x.1.2)
          ((x.1.1 root).lease.val - 1) := by
      rw [hstep]
      simp [resetClockBankRaceWeight, resetClockRawRaceWeight,
        hrank, hlease]
    have hbound := resetClockBankLiveRootLeaseBounds ring root x hg hl
    have hratio := resetClockRawLeaseDrop
      (2 * (compileAdvice q).b + 2)
      (compileAdvice q).bankLeaseCap
      (resetClockRank (compileAdvice q).b x.1.2)
      (x.1.1 root).lease.val hbound.1 hbound.2
    rw [hafter, hbefore]
    exact Nat.le_of_eq hratio
  · by_cases hwait :
        resetClockBankOutcome ring root x.1.1 x.1.2 e =
          .waitLoss
    · have hleaseOne := resetClockBankWaitLossLeaseOne
        ring x.1.1 root e hsp hc hgrant x.1.2 hs hwait
      have hchildWait :
          (resetClockBankComparisonNext ring root x e).2 =
            .waitLoss := by
        simp [resetClockBankComparisonNext, hl, hwait]
      have hchild :=
        resetClockBankRaceWeightAtFailure ring root
          (resetClockBankComparisonNext ring root x e) hchildWait
      have hbefore := resetClockRaceWeightLiveRaw ring root x hl
      have hbound := resetClockBankLiveRankBounds ring root x hg hl
      have hcap : 1 ≤ (compileAdvice q).bankLeaseCap := by
        change 1 ≤ 13 * ((compileAdvice q).b + 2)
        omega
      have hratio := resetClockRawTimeoutBound
        (2 * (compileAdvice q).b + 2)
        (compileAdvice q).bankLeaseCap
        (resetClockRank (compileAdvice q).b x.1.2)
        hbound.2 hcap
      calc
        4 * resetClockBankRaceWeight ring root
            (resetClockBankComparisonNext ring root x e) =
          4 * resetClockBankRaceScale q := by rw [hchild]
        _ ≤ 5 * resetClockRawRaceWeight
              (2 * (compileAdvice q).b + 2)
              (compileAdvice q).bankLeaseCap
              (resetClockRank (compileAdvice q).b x.1.2) 1 := by
          simpa only [resetClockBankRaceScale, Compiled.bankLeaseCap]
            using hratio
        _ = 5 * resetClockBankRaceWeight ring root x := by
          rw [hleaseOne.2] at hbefore
          rw [hbefore]
    · have hzero := resetClockBankRaceOtherExitZero
        ring root x e hl hout hwait
      rw [hzero]
      exact Nat.zero_le _

/-- The missing hdrift is discharged by the three-edge
local bounds on the actual comparison, with no added hypotheses. -/
theorem resetClockBankRaceDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ x : ResetClockBankComparisonState q n,
      ResetClockBankComparisonGood ring root x →
      x.2 = .live →
      (List.ofFn (fun e : Fin n =>
        resetClockBankRaceWeight ring root
          (resetClockBankComparisonNext ring root x e))).sum ≤
        n * resetClockBankRaceWeight ring root x := by
  exact resetClockBankRaceDriftOfLocalBounds ring root hsp
    (fun x hx hl => resetClockBankRaceProductiveEdge
      ring root hsp x hx hl)
    (fun x hx hl => resetClockBankRaceIncidentEdge
      ring root hsp x hx hl root (Or.inl rfl))
    (fun x hx hl e he => resetClockBankRaceIncidentEdge
      ring root hsp x hx hl e (Or.inr he))

/-- Unconditional finite-horizon C.1 weighted failure bound
in the genuine FiniteUniformStoppingTree API. -/
theorem resetClockBankTreeFailureBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ x : ResetClockBankComparisonState q n,
      ResetClockBankComparisonGood ring root x →
      ∀ T,
        resetClockBankRaceScale q *
          failureCount (resetClockBankTreeStep ring root)
            (resetClockBankTreeNode x) T ≤
          n ^ T * resetClockBankRaceWeight ring root x := by
  exact resetClockBankTreeFailureOfRaceDrift ring root hsp
    (resetClockBankRaceDrift ring root hsp)

end Counter
end L3


/-!
The full-lease initial value and numerical C.1 half bound.

At a genuine BANK reset launch the stage rank is 2b-1, the
lease cap is 13(b+2), and the conservative budget is L=2b+2.
The abstract inequality below reduces 2*W < scale exactly to
the watchdog_half certificate without large
nonlinear literal normalization.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree

/-- The numerical initial-bound lemma with *abstract* variables.
It is equivalent to the paper's half-watchdog inequality after
factoring the full-lease race weight. -/
theorem resetClockRawInitialHalf
    (L d rank : Nat) (hr : rank ≤ L)
    (hw : 2 * (2 ^ L * 4 ^ d) < 5 ^ d) :
    2 * resetClockRawRaceWeight L (L + d) rank (L + d) <
      2 ^ L * 5 ^ (L + d) := by
  have hpowTwo : 2 ^ (L - rank) ≤ 5 ^ (L - rank) :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 5) (L - rank)
  have hpowFive : 5 ^ L = 5 ^ rank * 5 ^ (L - rank) := by
    have h : rank + (L - rank) = L := by omega
    calc
      5 ^ L = 5 ^ (rank + (L - rank)) := by rw [h]
      _ = 5 ^ rank * 5 ^ (L - rank) := by rw [Nat.pow_add]
  have hraw :
      resetClockRawRaceWeight L (L + d) rank (L + d) =
        5 ^ rank * 4 ^ (L + d) * 2 ^ (L - rank) := by
    simp [resetClockRawRaceWeight]
  have hmono :
      5 ^ rank * 4 ^ (L + d) * 2 ^ (L - rank) ≤
        5 ^ L * 4 ^ (L + d) := by
    calc
      5 ^ rank * 4 ^ (L + d) * 2 ^ (L - rank) ≤
          5 ^ rank * 4 ^ (L + d) * 5 ^ (L - rank) :=
        Nat.mul_le_mul_left _ hpowTwo
      _ = 5 ^ L * 4 ^ (L + d) := by
        rw [hpowFive]
        ac_rfl
  have hfour : 4 ^ L = 2 ^ L * 2 ^ L := by
    have hh := Nat.mul_pow 2 2 L
    simpa using hh
  have hp : 0 < 5 ^ L * 2 ^ L :=
    Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))
  have hh := Nat.mul_lt_mul_of_pos_right hw hp
  calc
    2 * resetClockRawRaceWeight L (L + d) rank (L + d) ≤
        2 * (5 ^ L * 4 ^ (L + d)) := by
      rw [hraw]
      exact Nat.mul_le_mul_left _ hmono
    _ = (2 * (2 ^ L * 4 ^ d)) * (5 ^ L * 2 ^ L) := by
      rw [Nat.pow_add, hfour]
      ac_rfl
    _ < 5 ^ d * (5 ^ L * 2 ^ L) := hh
    _ = 2 ^ L * 5 ^ (L + d) := by
      rw [Nat.pow_add]
      ac_rfl

/-- A genuine postlaunch BANK front has initial failure race
weight strictly below half of the chosen integer denominator.
This is stronger than the C.1 estimate needed for C.2 renewal.
No explicit large compiled numerals are normalized. -/
theorem resetClockBankLaunchWeightHalf {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hlaunch : ResetLaunchPhysical ring C root) :
    2 * resetClockBankRaceWeight ring root
      ((C, .outward 1), .live) <
      resetClockBankRaceScale q := by
  obtain ⟨_, _, _, _, _, _, hlease⟩ := hlaunch
  have hcap :
      (compileAdvice q).bankLeaseCap =
        (2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24) := by
    change 13 * ((compileAdvice q).b + 2) =
      2 * (compileAdvice q).b + 2 +
        (11 * (compileAdvice q).b + 24)
    omega
  have hleaseCap :
      (C root).lease.val = (compileAdvice q).bankLeaseCap := by
    change (C root).lease.val =
      13 * ((compileAdvice q).b + 2)
    exact hlease
  have hr :
      2 * (compileAdvice q).b - 1 ≤
        2 * (compileAdvice q).b + 2 := by omega
  have hw := watchdog_half (compileAdvice q).b
  have hraw := resetClockRawInitialHalf
    (2 * (compileAdvice q).b + 2)
    (11 * (compileAdvice q).b + 24)
    (2 * (compileAdvice q).b - 1)
    hr hw
  have heq :
      resetClockBankRaceWeight ring root
        ((C, .outward 1), .live) =
      resetClockRawRaceWeight
        (2 * (compileAdvice q).b + 2)
        ((2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24))
        (2 * (compileAdvice q).b - 1)
        ((2 * (compileAdvice q).b + 2) +
          (11 * (compileAdvice q).b + 24)) := by
    have hh := resetClockRaceWeightLiveRaw
      ring root ((C, .outward 1), .live) rfl
    simpa only [resetClockRank, hleaseCap, hcap] using hh
  rw [heq]
  simpa only [resetClockBankRaceScale, hcap] using hraw

/-- Abstract arithmetic for the half-mass conclusion: a scaled
failure count bounded by a weight that is below half the scale.
Stated over variables so that no compiled literal is unfolded. -/
theorem resetClockHalfOfScaledWeight (S F W N : Nat)
    (hS : 0 < S) (hN : 0 < N)
    (h1 : S * F ≤ N * W) (h2 : 2 * W < S) :
    2 * F < N := by
  have h3 : S * (2 * F) < S * N := by
    calc
      S * (2 * F) = 2 * (S * F) := Nat.mul_left_comm S 2 F
      _ ≤ 2 * (N * W) := Nat.mul_le_mul_left 2 h1
      _ = N * (2 * W) := Nat.mul_left_comm 2 N W
      _ < N * S := Nat.mul_lt_mul_of_pos_left h2 hN
      _ = S * N := Nat.mul_comm N S
  exact (Nat.mul_lt_mul_left hS).mp h3

/-- The actual comparison's waitLoss exit has uniformly less than
one-half mass at every finite scheduler horizon. Defect, grant
and successful exit are NOT counted as failures. -/
theorem resetClockBankLaunchFailureHalf {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (C : Config q n)
    (hlaunch : ResetLaunchPhysical ring C root)
    (T : Nat) :
    2 * failureCount (resetClockBankTreeStep ring root)
      (resetClockBankTreeNode ((C, .outward 1), .live)) T <
      n ^ T := by
  have hg :=
    resetClockBankComparisonGoodLaunch ring root C hlaunch
  have hweight := resetClockBankTreeFailureBound
    ring root hsp ((C, .outward 1), .live) hg T
  have hhalf := resetClockBankLaunchWeightHalf
    ring root C hlaunch
  have hscale : 0 < resetClockBankRaceScale q := by
    unfold resetClockBankRaceScale
    exact Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))
  have hp : 0 < n ^ T := Nat.pow_pos ring.hn
  exact resetClockHalfOfScaledWeight
    (resetClockBankRaceScale q)
    (failureCount (resetClockBankTreeStep ring root)
      (resetClockBankTreeNode ((C, .outward 1), .live)) T)
    (resetClockBankRaceWeight ring root ((C, .outward 1), .live))
    (n ^ T) hscale hp hweight hhalf

end Counter
end L3


/-!
First physical restart prerequisite after a waitLoss exit.

A genuine role-stable BANK watchdog exit puts the root into
RESET with lease zero. This is weaker than an authenticated
fresh ResetLaunchPhysical snapshot and therefore does not by
itself establish the paper's C.2 renewal retry kernel.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical

/-- The BANK comparison's watchdog exit has an actual RESET
root with zero lease. This does not assume workers were erased
elsewhere or a fresh launch has occurred already. -/
theorem resetClockBankWaitLossRootReset {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hwait : resetClockBankOutcome ring root C s e = .waitLoss) :
    (((protocol q).step ring C e) root).mode = .RESET ∧
      (((protocol q).step ring C e) root).lease.val = 0 := by
  have hnoDef : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hd
    have heq :
        resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hd]
    rw [heq] at hwait
    cases hwait
  have hnotFinal : ¬ (e = root ∧ s = .returning 1) := by
    intro hf
    exact (resetClockBankFinalOutcomeTerminal
      ring C root e s hf).2 hwait
  have hlease := resetClockBankWaitLossLeaseOne
    ring C root e hsp hc hg s hs hwait
  have hw : ResetRootWaiting C root := by
    cases s with
    | finished =>
        cases hs
    | outward j =>
        exact hs.1
    | returning j =>
        exact hs.1
  have hp : ResetTrialPhysical ring C root :=
    resetClockStageToTrial ring C root s hs
  rcases hlease.1 with hroot | hincoming
  · subst e
    have hstage : s ≠ .returning 1 := by
      intro hf
      exact hnotFinal ⟨rfl, hf⟩
    have htok := resetClockFirstDigitNonfinal
      ring C root s hs hstage
    have hrow := resetClockOutgoingWaitPhysical
      ring C root hc hp hsp hg hw htok
    constructor
    · rw [hrow.1, hlease.2]
      simp [resetClockWaitMode]
    · rw [hrow.2, hlease.2]
      simp [resetClockWaitLease]
  · have hrow := resetClockIncomingWaitPhysical
      ring C root e hc hp hsp hg hw hincoming hnoDef
    constructor
    · rw [hrow.1, hlease.2]
      simp [resetClockWaitMode]
    · rw [hrow.2, hlease.2]
      simp [resetClockWaitLease]

end Counter
end L3

/-!
Native RESET recovery and launch-seeded renewal.

New recovery
steps execute the actual protocol. Defect and grant exits remain
distinct stopped-comparison outcomes and are never watchdog retries.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open PPL.Convergence.LDLocal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Physical recovery domain; remote worker scratch is unrestricted. -/
def ResetClockBankRestartReady {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : Prop :=
  Complete ring C root ∧ GrantFree C root ∧
    (C root).mode = .RESET

/-- Literal RESET launch precedes every return-token branch. -/
theorem resetClockBankRestartLaunchSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET)
    (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.mode = .RWAIT ∧
    (bankPair x y 1 b theta).1.lease = 13 * (b + 2) ∧
    (bankPair x y 1 b theta).2.bit = false ∧
    (bankPair x y 1 b theta).2.tok = .RR := by
  simp [bankPair, hx, hy, hg, hm, hb]

/-- A real root outgoing edge creates an authentic launch cut,
provided its actual successor has not taken the grant stop. -/
theorem resetClockBankRestartLaunch {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hready : ResetClockBankRestartReady ring C root)
    (hgnew : GrantFree ((protocol q).step ring C root) root) :
    ResetLaunchPhysical ring
      ((protocol q).step ring C root) root := by
  obtain ⟨hc, hg, hm⟩ := hready
  have hb : 1 ≤ (compileAdvice q).b :=
    Nat.le_of_lt (resetTrialCompiledWidth q)
  have hbpos : 0 < (compileAdvice q).b :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1) hb
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (Nat.zero_le _)
  have hone :
      (C (ring.rightNeighbor root)).pack.val = 1 := by
    simpa only [site] using hc 1 hb
  have hne : ring.rightNeighbor root ≠ root := by
    simpa only [site] using resetCompleteSitesDifferent ring C root hc 1 0 hb (Nat.zero_le _) (by decide)
  have hpost :
      packNext (C root).pack.val
        (C (ring.rightNeighbor root)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hbpos]
  have hrow :
      ((resetBankOld
        (C root) (C (ring.rightNeighbor root))).1).mode =
          .RWAIT ∧
      ((resetBankOld
        (C root) (C (ring.rightNeighbor root))).1).lease =
          13 * ((compileAdvice q).b + 2) ∧
      ((resetBankOld
        (C root) (C (ring.rightNeighbor root))).2).bit =
          false ∧
      ((resetBankOld
        (C root) (C (ring.rightNeighbor root))).2).tok =
          .RR := by
    have hh := resetClockBankRestartLaunchSymbolic
      (bankCell (C root) (C root).pack.val)
      (bankCell (C (ring.rightNeighbor root))
        (C (ring.rightNeighbor root)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C (ring.rightNeighbor root)).pack.val = 1; exact hone)
      (by change (C root).grant = false; exact hg)
      (by change (C root).mode = .RESET; exact hm) hb
    simpa only [resetBankOld, hpost, bankCell] using hh
  have htrip :=
    resetPhysicalEdgeBankTrip ring C root hne hsp
  have hmode := congrArg
    (fun z : Mode × Bool × BTok => z.1) htrip.1
  change (((protocol q).step ring C root) root).mode =
    ((resetBankOld
      (C root) (C (ring.rightNeighbor root))).1).mode
    at hmode
  have hbits := resetTrialTripBitTok
    (((protocol q).step ring C root)
      (ring.rightNeighbor root))
    ((resetBankOld
      (C root) (C (ring.rightNeighbor root))).2) htrip.2
  have hbound :
      ((resetBankOld
        (C root) (C (ring.rightNeighbor root))).1).lease <
          (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2.1]
    change
      13 * ((compileAdvice q).b + 2) <
        13 * ((compileAdvice q).b + 2) + 1
    exact Nat.lt_succ_self _
  have hcopy := resetClockCopyBankLeaseExact (C root)
    ((resetBankOld
      (C root) (C (ring.rightNeighbor root))).1) hbound
  have hlease :
      (((protocol q).step ring C root) root).lease.val =
        13 * ((compileAdvice q).b + 2) := by
    exact (congrArg Fin.val (resetClockPhysicalEdgeLeasePair ring C root hne hsp).1).trans (hcopy.trans hrow.2.1)
  have hcnew :
      Complete ring ((protocol q).step ring C root) root := by
    intro j hj
    have hh := congrFun
      (internal_roles_fixed ring C root 0 hc hbpos)
      (site ring root j)
    change
      (((protocol q).step ring C root)
        (site ring root j)).pack =
          (C (site ring root j)).pack at hh
    rw [hh]
    exact hc j hj
  refine ⟨hcnew, hgnew, hb,
    ⟨hmode.trans hrow.1, ?_⟩, ?_, ?_, hlease⟩
  · rw [hlease]
    exact Nat.mul_pos (by decide : 0 < 13) (Nat.zero_lt_succ _)
  · change
      (((protocol q).step ring C root)
        (ring.rightNeighbor root)).bit = false
    exact hbits.1.trans hrow.2.2.1
  · change
      (((protocol q).step ring C root)
        (ring.rightNeighbor root)).tok = .RR
    exact hbits.2.trans hrow.2.2.2

/-- A genuine watchdog exit supplies every recovery prerequisite. -/
theorem resetClockBankWaitLossRestartReady {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s)
    (hwait :
      resetClockBankOutcome ring root C s e = .waitLoss) :
    ResetClockBankRestartReady ring
      ((protocol q).step ring C e) root := by
  have hnoDef :
      ¬ ResetClockBankDefectEntry ring C root e := by
    intro hd
    have heq :
        resetClockBankOutcome ring root C s e = .defect := by
      simp [resetClockBankOutcome, hd]
    rw [heq] at hwait
    cases hwait
  have hnotFinal :
      ¬ (e = root ∧ s = .returning 1) := by
    intro hf
    exact (resetClockBankFinalOutcomeTerminal
      ring C root e s hf).2 hwait
  have hgnew :
      GrantFree ((protocol q).step ring C e) root := by
    by_cases hh :
        GrantFree ((protocol q).step ring C e) root
    · exact hh
    · have heq :
          resetClockBankOutcome ring root C s e = .grant := by
        simp [resetClockBankOutcome, hnoDef, hnotFinal, hh]
      rw [heq] at hwait
      cases hwait
  have hstable :=
    resetClockBankStableOfNoDefect ring C root e hnoDef
  have hcnew :
      Complete ring ((protocol q).step ring C e) root := by
    intro j hj
    rw [hstable j hj]
    exact hc j hj
  exact ⟨hcnew, hgnew,
    (resetClockBankWaitLossRootReset
      ring C root e hsp hc hg s hs hwait).1⟩

/-- An incoming good nonroot-to-root edge preserves RESET. -/
theorem resetClockBankRestartIncomingSymbolic
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false) (hm : y.mode = .RESET) :
    (bankPair x y 0 b theta).2.mode = .RESET := by
  simp [bankPair, hx, hy, hg, hm, isWaitMode] <;>
    repeat (first | rfl | split)

/-- The incoming preservation statement for the actual protocol. -/
theorem resetClockBankRestartIncomingPhysical {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : GrantFree C root)
    (hm : (C root).mode = .RESET)
    (hpred : ring.rightNeighbor e = root)
    (hnoDef : ¬ ResetClockBankDefectEntry ring C root e) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  have hb : 0 < (compileAdvice q).b :=
    Nat.lt_trans (by decide : 0 < 1)
      (resetTrialCompiledWidth q)
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (Nat.zero_le _)
  have hgood :
      goodPair (compileAdvice q).b
        (C e).pack (C root).pack = true := by
    cases h : goodPair (compileAdvice q).b
        (C e).pack (C root).pack with
    | false =>
        exact False.elim (hnoDef ⟨Or.inl hpred, Or.inl (by rw [hpred]; exact h)⟩)
    | true =>
        rfl
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    have hh := congrArg Fin.val
      (roleUpdate_eq_self_of_good (compileAdvice q).b
        (C e).pack (C root).pack hgood)
    rw [roleUpdate_val] at hh
    exact hh.trans hroot
  have hx : (C e).pack.val ≠ 0 := by
    intro hz
    have hh :
        packNext (C e).pack.val (C root).pack.val
          (compileAdvice q).b = 1 := by
      rw [hz, hroot]
      simp [packNext, hb]
    have hbad : (0 : Nat) = 1 := hpost.symm.trans hh
    cases hbad
  have hne : ring.rightNeighbor e ≠ e := by
    intro he
    have heq : e = root := he.symm.trans hpred
    rw [heq] at hx
    exact hx hroot
  have hrow :
      ((resetBankOld (C e) (C root)).2).mode = .RESET := by
    have hh := resetClockBankRestartIncomingSymbolic
      (bankCell (C e) (C e).pack.val)
      (bankCell (C root) (C root).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C e).pack.val ≠ 0; exact hx)
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C root).grant = false; exact hg)
      (by change (C root).mode = .RESET; exact hm)
    simpa only [resetBankOld, hpost, bankCell] using hh
  have hmode := congrArg
    (fun z : Mode × Bool × BTok => z.1)
    (resetPhysicalEdgeBankTrip ring C e hne hsp).2
  change
    (((protocol q).step ring C e)
      (ring.rightNeighbor e)).mode =
        ((resetBankOld
          (C e) (C (ring.rightNeighbor e))).2).mode at hmode
  rw [hpred] at hmode
  exact hmode.trans hrow

/-- Every continuing nonroot recovery edge preserves readiness. -/
theorem resetClockBankRestartIdle {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hready : ResetClockBankRestartReady ring C root)
    (he : e ≠ root)
    (hnoDef : ¬ ResetClockBankDefectEntry ring C root e)
    (hgnew : GrantFree ((protocol q).step ring C e) root) :
    ResetClockBankRestartReady ring
      ((protocol q).step ring C e) root := by
  obtain ⟨hc, hg, hm⟩ := hready
  have hstable :=
    resetClockBankStableOfNoDefect ring C root e hnoDef
  refine ⟨?_, hgnew, ?_⟩
  · intro j hj
    rw [hstable j hj]
    exact hc j hj
  · by_cases hpred : ring.rightNeighbor e = root
    · exact resetClockBankRestartIncomingPhysical
        ring C root e hc hsp hg hm hpred hnoDef
    · rw [step_frame ring C e root (Ne.symm he) (Ne.symm hpred)]
      exact hm


/-- Valid live BANK phase; validity is part of the active carrier. -/
structure ResetClockBankRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) where
  physical : Config q n
  stage : ResetClockStage
  complete : Complete ring physical root
  grantFree : GrantFree physical root
  phase : resetClockStageAt ring physical root stage

abbrev ResetClockBankLaunchSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Config q n // ResetLaunchPhysical ring C root }

abbrev ResetClockBankRecovery {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Config q n // ResetClockBankRestartReady ring C root }

abbrev ResetClockBankAttempt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  ResetClockBankRun (q := q) ring root ⊕
    ResetClockBankRecovery (q := q) ring root

/-- Three distinct terminal meanings in the physical observer. -/
inductive ResetClockBankStop where
  | clean
  | grant
  | defect
  deriving DecidableEq, Repr

/-- A retry carries the actual newly launched configuration. -/
inductive ResetClockBankResult {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) where
  | active : ResetClockBankAttempt (q := q) ring root →
      ResetClockBankResult (q := q) ring root
  | retry : ResetClockBankLaunchSeed (q := q) ring root →
      ResetClockBankResult (q := q) ring root
  | stop : Config q n → ResetClockBankStop →
      ResetClockBankResult (q := q) ring root

def resetClockBankAttemptStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (seed : ResetClockBankLaunchSeed (q := q) ring root) :
    ResetClockBankAttempt (q := q) ring root :=
  .inl ⟨seed.val, .outward 1, seed.property.1,
    seed.property.2.1,
    resetClockLaunchStage ring seed.val root seed.property⟩

def resetClockBankAttemptConfig {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankAttempt (q := q) ring root → Config q n
  | .inl x => x.physical
  | .inr x => x.val

noncomputable def resetClockBankRunNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hlive : resetClockBankOutcome ring root
      x.physical x.stage e = .live) :
    ResetClockBankRun (q := q) ring root :=
  { physical := (protocol q).step ring x.physical e
    stage := resetClockNext ring root (compileAdvice q).b x.stage e
    complete := (resetClockBankOutcomeLiveAllowed ring x.physical root hsp x.complete x.grantFree x.stage x.phase e hlive).2.1
    grantFree := (resetClockBankOutcomeLiveAllowed ring x.physical root hsp x.complete x.grantFree x.stage x.phase e hlive).1.2.2.1
    phase := (resetClockBankOutcomeLiveAllowed ring x.physical root hsp x.complete x.grantFree x.stage x.phase e hlive).2.2 }

def resetClockBankRunRecovery {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hwait : resetClockBankOutcome ring root
      x.physical x.stage e = .waitLoss) :
    ResetClockBankRecovery (q := q) ring root :=
  ⟨(protocol q).step ring x.physical e,
    resetClockBankWaitLossRestartReady ring x.physical root e hsp
      x.complete x.grantFree x.stage x.phase hwait⟩

/-- One actual scheduled edge. The recovery phase checks defect
and successor grant before constructing a launch-seed retry. -/
noncomputable def resetClockBankAttemptService {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetClockBankAttempt (q := q) ring root → Fin n →
      ResetClockBankResult (q := q) ring root
  | .inl x, e =>
      match hout : resetClockBankOutcome ring root
          x.physical x.stage e with
      | .live =>
          .active (.inl (resetClockBankRunNext ring root hsp x e hout))
      | .waitLoss =>
          .active (.inr (resetClockBankRunRecovery ring root hsp x e hout))
      | .success =>
          .stop ((protocol q).step ring x.physical e) .clean
      | .grant =>
          .stop ((protocol q).step ring x.physical e) .grant
      | .defect =>
          .stop ((protocol q).step ring x.physical e) .defect
  | .inr x, e =>
      if hd : ResetClockBankDefectEntry ring x.val root e then
        .stop ((protocol q).step ring x.val e) .defect
      else if hg : GrantFree ((protocol q).step ring x.val e) root then
        if he : e = root then
          .retry ⟨(protocol q).step ring x.val e,
            (by simpa only [he] using resetClockBankRestartLaunch ring x.val root hsp x.property (by simpa only [he] using hg))⟩
        else
          .active (.inr ⟨(protocol q).step ring x.val e,
            resetClockBankRestartIdle ring x.val root e hsp
              x.property he hd hg⟩)
      else
        .stop ((protocol q).step ring x.val e) .grant

def resetClockBankResultNode {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankResult (q := q) ring root →
      AttemptNode (ResetClockBankAttempt (q := q) ring root)
        (ResetClockBankLaunchSeed (q := q) ring root)
  | .active a => .active a
  | .retry seed => .retry seed
  | .stop _ _ => .success

/-- There are no invalid launch seeds: their physical proof is carried
in the subtype. The step never returns retry at the timeout cut. -/
noncomputable def resetClockBankRetryKernel {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    RetryKernel (ResetClockBankAttempt (q := q) ring root)
      (ResetClockBankLaunchSeed (q := q) ring root) n :=
  { start := resetClockBankAttemptStart ring root
    step := fun a e => resetClockBankResultNode ring root
      (resetClockBankAttemptService ring root hsp a e)
    valid := fun _ => True
    retry_valid := by intro a e seed h; trivial }

def resetClockBankResultConfig {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankResult (q := q) ring root → Config q n
  | .active a => resetClockBankAttemptConfig ring root a
  | .retry seed => seed.val
  | .stop C _ => C


/-!
Outcome equation interface for the actual dependent match.
Each run-side proof splits the dependent match itself; a bare
cases/rw on the scrutinee does not reduce this owner.
-/

theorem resetClockBankAttemptServiceLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (h : resetClockBankOutcome ring root x.physical x.stage e = .live) :
    resetClockBankAttemptService ring root hsp (.inl x) e =
      .active (.inl (resetClockBankRunNext ring root hsp x e h)) := by
  rw [resetClockBankAttemptService.eq_1]
  split
  all_goals
    first
    | rfl
    | (rename_i hcase; cases (h.symm.trans hcase))

theorem resetClockBankAttemptServiceWait {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (h : resetClockBankOutcome ring root x.physical x.stage e = .waitLoss) :
    resetClockBankAttemptService ring root hsp (.inl x) e =
      .active (.inr (resetClockBankRunRecovery ring root hsp x e h)) := by
  rw [resetClockBankAttemptService.eq_1]
  split
  all_goals
    first
    | rfl
    | (rename_i hcase; cases (h.symm.trans hcase))

theorem resetClockBankAttemptServiceSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (h : resetClockBankOutcome ring root x.physical x.stage e = .success) :
    resetClockBankAttemptService ring root hsp (.inl x) e =
      .stop ((protocol q).step ring x.physical e) .clean := by
  rw [resetClockBankAttemptService.eq_1]
  split
  all_goals
    first
    | rfl
    | (rename_i hcase; cases (h.symm.trans hcase))

theorem resetClockBankAttemptServiceGrant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (h : resetClockBankOutcome ring root x.physical x.stage e = .grant) :
    resetClockBankAttemptService ring root hsp (.inl x) e =
      .stop ((protocol q).step ring x.physical e) .grant := by
  rw [resetClockBankAttemptService.eq_1]
  split
  all_goals
    first
    | rfl
    | (rename_i hcase; cases (h.symm.trans hcase))

theorem resetClockBankAttemptServiceDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (h : resetClockBankOutcome ring root x.physical x.stage e = .defect) :
    resetClockBankAttemptService ring root hsp (.inl x) e =
      .stop ((protocol q).step ring x.physical e) .defect := by
  rw [resetClockBankAttemptService.eq_1]
  split
  all_goals
    first
    | rfl
    | (rename_i hcase; cases (h.symm.trans hcase))

/-- Recovery branch: actual defect and grant exits. -/
theorem resetClockBankAttemptServiceRecoverDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (e : Fin n)
    (hd : ResetClockBankDefectEntry ring x.val root e) :
    resetClockBankAttemptService ring root hsp (.inr x) e =
      .stop ((protocol q).step ring x.val e) .defect := by
  simp only [resetClockBankAttemptService, dif_pos hd]

theorem resetClockBankAttemptServiceRecoverGrant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : ¬ GrantFree ((protocol q).step ring x.val e) root) :
    resetClockBankAttemptService ring root hsp (.inr x) e =
      .stop ((protocol q).step ring x.val e) .grant := by
  simp only [resetClockBankAttemptService, dif_neg hd, dif_neg hg]

/-- The existential result avoids exposing the proof field of the
authentic new launch seed, while preserving exact physical custody. -/
theorem resetClockBankAttemptServiceRecoverRetry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : GrantFree ((protocol q).step ring x.val e) root)
    (he : e = root) :
    ∃ seed : ResetClockBankLaunchSeed (q := q) ring root,
      resetClockBankAttemptService ring root hsp (.inr x) e =
        .retry seed ∧
      seed.val = (protocol q).step ring x.val e := by
  subst e
  refine ⟨⟨(protocol q).step ring x.val root,
    resetClockBankRestartLaunch ring x.val root hsp x.property hg⟩,
    ?_, rfl⟩
  simp only [resetClockBankAttemptService, dif_neg hd,
    dif_pos hg, dite_true]

theorem resetClockBankAttemptServiceRecoverContinue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : GrantFree ((protocol q).step ring x.val e) root)
    (he : e ≠ root) :
    ∃ y : ResetClockBankRecovery (q := q) ring root,
      resetClockBankAttemptService ring root hsp (.inr x) e =
        .active (.inr y) ∧
      y.val = (protocol q).step ring x.val e := by
  refine ⟨⟨(protocol q).step ring x.val e,
    resetClockBankRestartIdle ring x.val root e hsp
      x.property he hd hg⟩, ?_, rfl⟩
  simp only [resetClockBankAttemptService, dif_neg hd,
    dif_pos hg, dif_neg he]

/-- Exact custody for an owner step, with a genuine dependent
outcome equation rather than rewriting the nested match. -/
theorem resetClockBankServicePhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root) (e : Fin n) :
    resetClockBankResultConfig ring root
      (resetClockBankAttemptService ring root hsp a e) =
      (protocol q).step ring (resetClockBankAttemptConfig ring root a) e := by
  cases a with
  | inl x =>
      cases hout : resetClockBankOutcome ring root x.physical x.stage e with
      | live =>
          rw [resetClockBankAttemptServiceLive ring root hsp x e hout]
          rfl
      | waitLoss =>
          rw [resetClockBankAttemptServiceWait ring root hsp x e hout]
          rfl
      | success =>
          rw [resetClockBankAttemptServiceSuccess ring root hsp x e hout]
          rfl
      | grant =>
          rw [resetClockBankAttemptServiceGrant ring root hsp x e hout]
          rfl
      | defect =>
          rw [resetClockBankAttemptServiceDefect ring root hsp x e hout]
          rfl
  | inr x =>
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankAttemptServiceRecoverDefect ring root hsp x e hd]
        rfl
      · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
        · by_cases he : e = root
          · obtain ⟨seed, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverRetry
                ring root hsp x e hd hg he
            rw [hs]
            exact hv
          · obtain ⟨y, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverContinue
                ring root hsp x e hd hg he
            rw [hs]
            exact hv
        · rw [resetClockBankAttemptServiceRecoverGrant ring root hsp x e hd hg]
          rfl

/-- Every retry is at the actual selected edge's authentic launch cut. -/
theorem resetClockBankRetryAuthentic {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root) (e : Fin n)
    (seed : ResetClockBankLaunchSeed (q := q) ring root)
    (h : (resetClockBankRetryKernel ring root hsp).step a e = .retry seed) :
    ResetLaunchPhysical ring seed.val root ∧
      seed.val =
        (protocol q).step ring (resetClockBankAttemptConfig ring root a) e := by
  refine ⟨seed.property, ?_⟩
  have hp := resetClockBankServicePhysical ring root hsp a e
  change resetClockBankResultNode ring root
    (resetClockBankAttemptService ring root hsp a e) = .retry seed at h
  cases hs : resetClockBankAttemptService ring root hsp a e with
  | active b =>
      have hh :
          (AttemptNode.active b :
            AttemptNode (ResetClockBankAttempt (q := q) ring root)
              (ResetClockBankLaunchSeed (q := q) ring root)) =
          .retry seed := by
        simpa only [hs, resetClockBankResultNode] using h
      cases hh
  | retry seed' =>
      have hh :
          (AttemptNode.retry seed' :
            AttemptNode (ResetClockBankAttempt (q := q) ring root)
              (ResetClockBankLaunchSeed (q := q) ring root)) =
          .retry seed := by
        simpa only [hs, resetClockBankResultNode] using h
      cases hh
      simpa only [hs, resetClockBankResultConfig] using hp
  | stop C reason =>
      have hh :
          (AttemptNode.success :
            AttemptNode (ResetClockBankAttempt (q := q) ring root)
              (ResetClockBankLaunchSeed (q := q) ring root)) =
          .retry seed := by
        simpa only [hs, resetClockBankResultNode] using h
      cases hh

/-- Abstract rank arithmetic, with no compiled constants in tactics. -/
theorem resetRenewalRankBalanceLe (a b k : Nat)
    (h : a + k = b) : a ≤ b := by
  omega

theorem resetRenewalInitialRank (b : Nat) (hb : 1 ≤ b) :
    (2 * b - 1) + 1 = 2 * b := by
  omega

def resetRenewalNodeRank {A Seed : Type} (rank : A → Nat) :
    AttemptNode A Seed → Nat
  | .active a => rank a
  | .success => 0
  | .retry _ => 0

def resetRenewalNodeChosen {A Seed : Type} {n : Nat}
    (fallback : Fin n) (chosen : A → Fin n) :
    AttemptNode A Seed → Fin n
  | .active a => chosen a
  | .success => fallback
  | .retry _ => fallback

/-- A nominated service pays the exact single-attempt API cost. -/
theorem resetRenewalAttemptCost {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (rank : A → Nat) (chosen : A → Fin n) (fallback : Fin n)
    (hdrop : ∀ a : A,
      resetRenewalNodeRank rank (K.step a (chosen a)) + 1 ≤ rank a)
    (hweak : ∀ (a : A) (e : Fin n),
      resetRenewalNodeRank rank (K.step a e) ≤ rank a)
    (a : A) (T : Nat) :
    attemptCostNumerator K (.active a) T ≤ n ^ T * (n * rank a) := by
  have hd : ∀ z : AttemptNode A Seed,
      ¬ (Prob.attemptGood z ∨ Prob.attemptFail z) →
      resetRenewalNodeRank rank
          (Prob.attemptStepper K z
            (resetRenewalNodeChosen fallback chosen z)) + 1 ≤
        resetRenewalNodeRank rank z := by
    intro z hz
    cases z with
    | active a => exact hdrop a
    | success => exact False.elim (hz (Or.inl True.intro))
    | retry seed => exact False.elim (hz (Or.inr True.intro))
  have hw : ∀ z : AttemptNode A Seed,
      ¬ (Prob.attemptGood z ∨ Prob.attemptFail z) →
      ∀ e : Fin n,
        resetRenewalNodeRank rank (Prob.attemptStepper K z e) ≤
          resetRenewalNodeRank rank z := by
    intro z hz e
    cases z with
    | active a => exact hweak a e
    | success => exact False.elim (hz (Or.inl True.intro))
    | retry seed => exact False.elim (hz (Or.inr True.intro))
  have hh := Prob.costNumerator_le_of_nominated_edge
    (Prob.attemptStepper K)
    (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
    (resetRenewalNodeRank rank)
    (resetRenewalNodeChosen fallback chosen)
    hd hw (.active a) T
  simpa only [Prob.attempt_costNumerator_eq, resetRenewalNodeRank] using hh

/-- Reserve one additional nominated root service for recovery. -/
def resetClockBankAttemptRank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankAttempt (q := q) ring root → Nat
  | .inl x => resetClockRank (compileAdvice q).b x.stage + 1
  | .inr _ => 1

def resetClockBankAttemptChosen {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankAttempt (q := q) ring root → Fin n
  | .inl x => resetClockNominated ring root (compileAdvice q).b x.stage
  | .inr _ => root

theorem resetClockBankRunRankPositive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankRun (q := q) ring root) :
    1 ≤ resetClockRank (compileAdvice q).b x.stage := by
  exact (resetClockBankLiveRankBounds ring root
    ((x.physical, x.stage), .live)
    (fun _ => ⟨x.complete, x.grantFree, x.phase⟩) rfl).1

/-- The nominated edge drops reserve, including the separate recovery service. -/
theorem resetClockBankAttemptDrop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ a : ResetClockBankAttempt (q := q) ring root,
      resetRenewalNodeRank (resetClockBankAttemptRank ring root)
        ((resetClockBankRetryKernel ring root hsp).step a
          (resetClockBankAttemptChosen ring root a)) + 1 ≤
        resetClockBankAttemptRank ring root a := by
  intro a
  cases a with
  | inl x =>
      have hr := resetClockBankRankStepExact ring x.physical root
        x.stage x.phase
        (resetClockNominated ring root (compileAdvice q).b x.stage)
      rw [if_pos rfl] at hr
      change
        resetRenewalNodeRank (resetClockBankAttemptRank ring root)
          (resetClockBankResultNode ring root
            (resetClockBankAttemptService ring root hsp (.inl x)
              (resetClockNominated ring root (compileAdvice q).b x.stage))) +
          1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
      cases hout : resetClockBankOutcome ring root x.physical x.stage
          (resetClockNominated ring root (compileAdvice q).b x.stage) with
      | live =>
          rw [resetClockBankAttemptServiceLive ring root hsp x _ hout]
          change (resetClockRank (compileAdvice q).b
            (resetClockNext ring root (compileAdvice q).b x.stage
              (resetClockNominated ring root (compileAdvice q).b x.stage)) +
              1) + 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.le_of_eq (congrArg (fun v : Nat => v + 1) hr)
      | waitLoss =>
          rw [resetClockBankAttemptServiceWait ring root hsp x _ hout]
          change 1 + 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.add_le_add_right
            (resetClockBankRunRankPositive ring root x) 1
      | success =>
          rw [resetClockBankAttemptServiceSuccess ring root hsp x _ hout]
          change 0 + 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
      | grant =>
          rw [resetClockBankAttemptServiceGrant ring root hsp x _ hout]
          change 0 + 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
      | defect =>
          rw [resetClockBankAttemptServiceDefect ring root hsp x _ hout]
          change 0 + 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
  | inr x =>
      change
        resetRenewalNodeRank (resetClockBankAttemptRank ring root)
          (resetClockBankResultNode ring root
            (resetClockBankAttemptService ring root hsp (.inr x) root)) +
          1 ≤ 1
      by_cases hd : ResetClockBankDefectEntry ring x.val root root
      · rw [resetClockBankAttemptServiceRecoverDefect ring root hsp x root hd]
        exact Nat.le_refl 1
      · by_cases hg : GrantFree ((protocol q).step ring x.val root) root
        · obtain ⟨seed, hs, hv⟩ :=
            resetClockBankAttemptServiceRecoverRetry
              ring root hsp x root hd hg rfl
          rw [hs]
          exact Nat.le_refl 1
        · rw [resetClockBankAttemptServiceRecoverGrant ring root hsp x root hd hg]
          exact Nat.le_refl 1

/-- No scheduled edge increases the single-attempt reserve. -/
theorem resetClockBankAttemptWeak {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (a : ResetClockBankAttempt (q := q) ring root) (e : Fin n),
      resetRenewalNodeRank (resetClockBankAttemptRank ring root)
        ((resetClockBankRetryKernel ring root hsp).step a e) ≤
        resetClockBankAttemptRank ring root a := by
  intro a e
  cases a with
  | inl x =>
      have hr := resetClockBankRankStepExact
        ring x.physical root x.stage x.phase e
      change
        resetRenewalNodeRank (resetClockBankAttemptRank ring root)
          (resetClockBankResultNode ring root
            (resetClockBankAttemptService ring root hsp (.inl x) e)) ≤
        resetClockRank (compileAdvice q).b x.stage + 1
      cases hout : resetClockBankOutcome ring root x.physical x.stage e with
      | live =>
          rw [resetClockBankAttemptServiceLive ring root hsp x e hout]
          change resetClockRank (compileAdvice q).b
            (resetClockNext ring root (compileAdvice q).b x.stage e) + 1 ≤
              resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.add_le_add_right (resetRenewalRankBalanceLe _ _ _ hr) 1
      | waitLoss =>
          rw [resetClockBankAttemptServiceWait ring root hsp x e hout]
          change 1 ≤ resetClockRank (compileAdvice q).b x.stage + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
      | success =>
          rw [resetClockBankAttemptServiceSuccess ring root hsp x e hout]
          exact Nat.zero_le _
      | grant =>
          rw [resetClockBankAttemptServiceGrant ring root hsp x e hout]
          exact Nat.zero_le _
      | defect =>
          rw [resetClockBankAttemptServiceDefect ring root hsp x e hout]
          exact Nat.zero_le _
  | inr x =>
      change
        resetRenewalNodeRank (resetClockBankAttemptRank ring root)
          (resetClockBankResultNode ring root
            (resetClockBankAttemptService ring root hsp (.inr x) e)) ≤ 1
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankAttemptServiceRecoverDefect ring root hsp x e hd]
        exact Nat.zero_le _
      · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
        · by_cases he : e = root
          · obtain ⟨seed, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverRetry
                ring root hsp x e hd hg he
            rw [hs]
            exact Nat.zero_le _
          · obtain ⟨y, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverContinue
                ring root hsp x e hd hg he
            rw [hs]
            exact Nat.le_refl 1
        · rw [resetClockBankAttemptServiceRecoverGrant ring root hsp x e hd hg]
          exact Nat.zero_le _

/-- Exact per-attempt cost from any carried physical phase. -/
theorem resetClockBankAttemptCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root) (T : Nat) :
    attemptCostNumerator (resetClockBankRetryKernel ring root hsp)
      (.active a) T ≤
      n ^ T * (n * resetClockBankAttemptRank ring root a) := by
  exact resetRenewalAttemptCost (resetClockBankRetryKernel ring root hsp)
    (resetClockBankAttemptRank ring root)
    (resetClockBankAttemptChosen ring root) root
    (resetClockBankAttemptDrop ring root hsp)
    (resetClockBankAttemptWeak ring root hsp) a T

/-- A launched race plus any following recovery costs at most 2bn. -/
theorem resetClockBankLaunchAttemptCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (seed : ResetClockBankLaunchSeed (q := q) ring root) (T : Nat) :
    attemptCostNumerator (resetClockBankRetryKernel ring root hsp)
      (.active ((resetClockBankRetryKernel ring root hsp).start seed)) T ≤
      n ^ T * (n * (2 * (compileAdvice q).b)) := by
  have hr :
      resetClockBankAttemptRank ring root
        ((resetClockBankRetryKernel ring root hsp).start seed) =
        2 * (compileAdvice q).b := by
    change (2 * (compileAdvice q).b - 1) + 1 = 2 * (compileAdvice q).b
    exact resetRenewalInitialRank (compileAdvice q).b seed.property.2.2.1
  have hh := resetClockBankAttemptCost ring root hsp
    ((resetClockBankRetryKernel ring root hsp).start seed) T
  rw [hr] at hh
  exact hh

/-- Initial or post-timeout RESET recovery costs at most n. -/
theorem resetClockBankRecoveryAttemptCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (T : Nat) :
    attemptCostNumerator (resetClockBankRetryKernel ring root hsp)
      (.active (.inr x)) T ≤ n ^ T * n := by
  have hh := resetClockBankAttemptCost ring root hsp (.inr x) T
  simpa only [resetClockBankAttemptRank, Nat.mul_one] using hh


/-- No finite first-retry event contains more than all scheduler words. -/
theorem resetRenewalRetryCountLePow {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (z : AttemptNode A Seed) (T : Nat),
      retryCount K z T ≤ n ^ T := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z with
      | active a => exact Nat.zero_le _
      | success => exact Nat.zero_le _
      | retry seed => exact Nat.le_refl _
  | succ T ih =>
      cases z with
      | success => exact Nat.zero_le _
      | retry seed => exact Nat.le_refl _
      | active a =>
          change
            (List.ofFn (fun e : Fin n =>
              retryCount K (K.step a e) T)).sum ≤ n ^ (T + 1)
          calc
            (List.ofFn (fun e : Fin n =>
                retryCount K (K.step a e) T)).sum ≤
                (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
              ofFn_sum_le _ _ (fun e => ih (K.step a e))
            _ = n * n ^ T := ofFn_sum_const n (n ^ T)
            _ = n ^ (T + 1) := by
              rw [Nat.pow_succ, Nat.mul_comm]

theorem resetRenewalRetrySuccessZero {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) (T : Nat) :
    retryCount K (.success) T = 0 := by
  cases T <;> rfl

/-- Delayed retries remain subevents of the original exact
watchdog's first wait-loss exit; recovery does not mint new failure mass. -/
theorem resetClockBankAttemptRetryLeFailure {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (T : Nat) (x : ResetClockBankRun (q := q) ring root),
      retryCount (resetClockBankRetryKernel ring root hsp)
        (.active (.inl x)) T ≤
      failureCount (resetClockBankTreeStep ring root)
        (resetClockBankTreeNode ((x.physical, x.stage), .live)) T := by
  intro T
  induction T with
  | zero =>
      intro x
      have hn :
          resetClockBankTreeNode ((x.physical, x.stage), .live) =
            .active ((x.physical, x.stage), .live) := by
        simp [resetClockBankTreeNode]
      rw [hn]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x
      have hn :
          resetClockBankTreeNode ((x.physical, x.stage), .live) =
            .active ((x.physical, x.stage), .live) := by
        simp [resetClockBankTreeNode]
      rw [hn]
      change
        (List.ofFn (fun e : Fin n =>
          retryCount (resetClockBankRetryKernel ring root hsp)
            ((resetClockBankRetryKernel ring root hsp).step (.inl x) e) T)).sum ≤
        (List.ofFn (fun e : Fin n =>
          failureCount (resetClockBankTreeStep ring root)
            (resetClockBankTreeStep ring root
              ((x.physical, x.stage), .live) e) T)).sum
      apply ofFn_sum_le
      intro e
      cases hout : resetClockBankOutcome ring root x.physical x.stage e with
      | live =>
          have hk :
              (resetClockBankRetryKernel ring root hsp).step (.inl x) e =
                .active (.inl (resetClockBankRunNext ring root hsp x e hout)) := by
            change resetClockBankResultNode ring root
              (resetClockBankAttemptService ring root hsp (.inl x) e) = _
            rw [resetClockBankAttemptServiceLive ring root hsp x e hout]
            rfl
          have hc :
              resetClockBankTreeStep ring root
                  ((x.physical, x.stage), .live) e =
                resetClockBankTreeNode
                  (((protocol q).step ring x.physical e,
                    resetClockNext ring root (compileAdvice q).b x.stage e),
                    .live) := by
            simp [resetClockBankTreeStep, resetClockBankComparisonNext, hout]
          rw [hk, hc]
          exact ih (resetClockBankRunNext ring root hsp x e hout)
      | waitLoss =>
          have hc :
              resetClockBankTreeStep ring root
                  ((x.physical, x.stage), .live) e = .failure := by
            simp [resetClockBankTreeStep, resetClockBankComparisonNext,
              resetClockBankTreeNode, hout]
          rw [hc, resetClockBankTreeFailureFull]
          exact resetRenewalRetryCountLePow
            (resetClockBankRetryKernel ring root hsp)
            ((resetClockBankRetryKernel ring root hsp).step (.inl x) e) T
      | success =>
          have hk :
              (resetClockBankRetryKernel ring root hsp).step (.inl x) e =
                .success := by
            change resetClockBankResultNode ring root
              (resetClockBankAttemptService ring root hsp (.inl x) e) = _
            rw [resetClockBankAttemptServiceSuccess ring root hsp x e hout]
            rfl
          rw [hk, resetRenewalRetrySuccessZero]
          exact Nat.zero_le _
      | grant =>
          have hk :
              (resetClockBankRetryKernel ring root hsp).step (.inl x) e =
                .success := by
            change resetClockBankResultNode ring root
              (resetClockBankAttemptService ring root hsp (.inl x) e) = _
            rw [resetClockBankAttemptServiceGrant ring root hsp x e hout]
            rfl
          rw [hk, resetRenewalRetrySuccessZero]
          exact Nat.zero_le _
      | defect =>
          have hk :
              (resetClockBankRetryKernel ring root hsp).step (.inl x) e =
                .success := by
            change resetClockBankResultNode ring root
              (resetClockBankAttemptService ring root hsp (.inl x) e) = _
            rw [resetClockBankAttemptServiceDefect ring root hsp x e hout]
            rfl
          rw [hk, resetRenewalRetrySuccessZero]
          exact Nat.zero_le _

/-- The strict C.1 half bound survives the delayed native recovery. -/
theorem resetClockBankAttemptRetryHalf {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (seed : ResetClockBankLaunchSeed (q := q) ring root)
    (T : Nat) :
    2 * retryCount (resetClockBankRetryKernel ring root hsp)
      (.active ((resetClockBankRetryKernel ring root hsp).start seed)) T <
      n ^ T := by
  have hd :
      retryCount (resetClockBankRetryKernel ring root hsp)
        (.active ((resetClockBankRetryKernel ring root hsp).start seed)) T ≤
      failureCount (resetClockBankTreeStep ring root)
        (resetClockBankTreeNode ((seed.val, .outward 1), .live)) T := by
    exact resetClockBankAttemptRetryLeFailure ring root hsp T
      ⟨seed.val, .outward 1, seed.property.1, seed.property.2.1,
        resetClockLaunchStage ring seed.val root seed.property⟩
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hd)
    (resetClockBankLaunchFailureHalf ring root hsp seed.val seed.property T)


/-- The stopped physical observer retains the exit reason and endpoint. -/
abbrev ResetClockBankRenewalState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  ResetClockBankAttempt (q := q) ring root ⊕
    (Config q n × ResetClockBankStop)

def resetClockBankRenewalConfig {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankRenewalState (q := q) ring root → Config q n
  | .inl a => resetClockBankAttemptConfig ring root a
  | .inr z => z.1

/-- This is the stopped local target, with three distinct exit labels. -/
def resetClockBankRenewalTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankRenewalState (q := q) ring root → Prop
  | .inl _ => False
  | .inr _ => True

def resetClockBankResultObserve {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankResult (q := q) ring root →
      ResetClockBankRenewalState (q := q) ring root
  | .active a => .inl a
  | .retry seed => .inl (resetClockBankAttemptStart ring root seed)
  | .stop C reason => .inr (C, reason)

noncomputable def resetClockBankRenewalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetClockBankRenewalState (q := q) ring root → Fin n →
      ResetClockBankRenewalState (q := q) ring root
  | .inl a, e => resetClockBankResultObserve ring root
      (resetClockBankAttemptService ring root hsp a e)
  | .inr z, _ => .inr z

theorem resetClockBankResultObservePhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankResult (q := q) ring root) :
    resetClockBankRenewalConfig ring root
      (resetClockBankResultObserve ring root z) =
      resetClockBankResultConfig ring root z := by
  cases z <;> rfl

/-- Until its explicit stop, the observer follows one real edge
per scheduler letter, including the launch that produces a retry. -/
theorem resetClockBankRenewalPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRenewalState (q := q) ring root)
    (hx : ¬ resetClockBankRenewalTarget ring root x) (e : Fin n) :
    resetClockBankRenewalConfig ring root
      (resetClockBankRenewalNext ring root hsp x e) =
      (protocol q).step ring
        (resetClockBankRenewalConfig ring root x) e := by
  cases x with
  | inl a =>
      change resetClockBankRenewalConfig ring root
        (resetClockBankResultObserve ring root
          (resetClockBankAttemptService ring root hsp a e)) = _
      rw [resetClockBankResultObservePhysical]
      exact resetClockBankServicePhysical ring root hsp a e
  | inr z =>
      exact False.elim (hx True.intro)

/-- Pure constructor algebra for the actual stopped result.
No dependent outcome match is opened in this simulation. -/
theorem resetClockBankResultSimulationClause {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankResult (q := q) ring root) :
    match resetClockBankResultNode ring root z with
    | .success =>
        resetClockBankRenewalTarget ring root
          (resetClockBankResultObserve ring root z)
    | .active a' =>
        resetClockBankResultObserve ring root z = .inl a'
    | .retry seed =>
        resetClockBankResultObserve ring root z =
          .inl (resetClockBankAttemptStart ring root seed) := by
  cases z with
  | active b => rfl
  | retry seed => rfl
  | stop C reason => exact True.intro

/-- Same-letter restart simulation, including the retry-as-new-launch cut. -/
theorem resetClockBankRenewalSimulation {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    Prob.RetrySimulation (resetClockBankRetryKernel ring root hsp)
      (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root)
      (fun x a => x = .inl a) := by
  intro x a hrel hx e
  cases hrel
  have hk : (resetClockBankRetryKernel ring root hsp).step a e =
      resetClockBankResultNode ring root
        (resetClockBankAttemptService ring root hsp a e) := rfl
  have hn : resetClockBankRenewalNext ring root hsp (Sum.inl a) e =
      resetClockBankResultObserve ring root
        (resetClockBankAttemptService ring root hsp a e) := rfl
  rw [hk, hn]
  have hclause := resetClockBankResultSimulationClause ring root
    (resetClockBankAttemptService ring root hsp a e)
  revert hclause
  cases resetClockBankResultNode ring root
      (resetClockBankAttemptService ring root hsp a e) <;>
    exact id

/-- Exact ceiling arithmetic over an abstract variable. -/
theorem resetRenewalHalfCeiling (B : Nat) :
    Prob.renewalCeiling B 1 2 = 2 * B := by
  change B * 2 / 1 + (if B * 2 % 1 = 0 then 0 else 1) = 2 * B
  rw [Nat.div_one, Nat.mod_one, if_pos rfl, Nat.add_zero]
  exact Nat.mul_comm B 2

/-- C.2 launch-seeded renewal, using the native attempt cost and
delayed retryCount in the geometric-ceiling theorem. -/
theorem resetClockBankLaunchRenewalCeiling {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (seed : ResetClockBankLaunchSeed (q := q) ring root) :
    ∀ T : Nat,
      costNumerator (resetClockBankRenewalNext ring root hsp)
        (resetClockBankRenewalTarget ring root)
        (.inl (resetClockBankAttemptStart ring root seed)) T ≤
      n ^ T *
        Prob.renewalCeiling (n * (2 * (compileAdvice q).b)) 1 2 := by
  refine Prob.costNumerator_renewal_le
    (resetClockBankRenewalNext ring root hsp)
    (resetClockBankRenewalTarget ring root)
    (resetClockBankRetryKernel ring root hsp)
    (fun x a => x = .inl a)
    (resetClockBankRenewalSimulation ring root hsp)
    (n * (2 * (compileAdvice q).b)) 1 2 (by decide) ?_ ?_
    (.inl (resetClockBankAttemptStart ring root seed)) seed
    True.intro rfl
  · intro s hs T
    rw [Prob.attempt_costNumerator_eq]
    exact resetClockBankLaunchAttemptCost ring root hsp s T
  · intro s hs T
    simpa only [Nat.one_mul] using Nat.le_of_lt (resetClockBankAttemptRetryHalf ring root hsp s T)

theorem resetClockBankLaunchRenewalCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (seed : ResetClockBankLaunchSeed (q := q) ring root) (T : Nat) :
    costNumerator (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root)
      (.inl (resetClockBankAttemptStart ring root seed)) T ≤
      n ^ T * (2 * (n * (2 * (compileAdvice q).b))) := by
  have hh := resetClockBankLaunchRenewalCeiling ring root hsp seed T
  rw [resetRenewalHalfCeiling] at hh
  exact hh

/-- The physical cut reached when recovery ends in a launch. -/
def resetClockBankRenewalLaunchCut {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankRenewalState (q := q) ring root) : Prop :=
  ∃ seed : ResetClockBankLaunchSeed (q := q) ring root,
    x = .inl (resetClockBankAttemptStart ring root seed)

/-- Same-letter transfer to the first success-or-retry cut. -/
theorem resetClockCostLeAttemptStop {X A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n)
    (next : X → Fin n → X)
    (P Acut : X → Prop) (Rel : X → A → Prop)
    (hstep : ∀ (x : X) (a : A), Rel x a →
      ¬ (P x ∨ Acut x) → ∀ e : Fin n,
        match K.step a e with
        | .success => P (next x e)
        | .retry _ => Acut (next x e)
        | .active a' => Rel (next x e) a') :
    ∀ (x : X) (a : A), Rel x a → ∀ T : Nat,
      costNumerator next (fun y => Acut y ∨ P y) x T ≤
        attemptCostNumerator K (.active a) T := by
  intro x a hrel T
  induction T generalizing x a with
  | zero =>
      change 0 ≤ 0
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hx : Acut x ∨ P x
      · rw [costNumerator_terminal next
          (fun y => Acut y ∨ P y) x hx (T + 1)]
        exact Nat.zero_le _
      · have hnot : ¬ (P x ∨ Acut x) := by
          intro h
          rcases h with hp | ha
          · exact hx (Or.inr hp)
          · exact hx (Or.inl ha)
        rw [costNumerator_succ next
          (fun y => Acut y ∨ P y) x hx T]
        change n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              costNumerator next (fun y => Acut y ∨ P y)
                (next x e) T)).sum ≤
          n ^ (T + 1) +
            (List.ofFn (fun e : Fin n =>
              attemptCostNumerator K (K.step a e) T)).sum
        have hc (e : Fin n) :
            costNumerator next (fun y => Acut y ∨ P y)
                (next x e) T ≤
              attemptCostNumerator K (K.step a e) T := by
          have hh := hstep x a hrel hnot e
          cases he : K.step a e with
          | success =>
              have hp : P (next x e) := by
                simpa only [he] using hh
              rw [costNumerator_terminal next
                (fun y => Acut y ∨ P y)
                (next x e) (Or.inr hp) T]
              exact Nat.zero_le _
          | retry s =>
              have ha : Acut (next x e) := by
                simpa only [he] using hh
              rw [costNumerator_terminal next
                (fun y => Acut y ∨ P y)
                (next x e) (Or.inl ha) T]
              exact Nat.zero_le _
          | active a' =>
              have hr : Rel (next x e) a' := by
                simpa only [he] using hh
              exact ih (next x e) a' hr
        exact Nat.add_le_add_left (ofFn_sum_le _ _ hc) _

/-- Same result algebra for the first-launch stage target. -/
theorem resetClockBankResultLaunchClause {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankResult (q := q) ring root) :
    match resetClockBankResultNode ring root z with
    | .success =>
        resetClockBankRenewalTarget ring root
          (resetClockBankResultObserve ring root z)
    | .retry _ =>
        resetClockBankRenewalLaunchCut ring root
          (resetClockBankResultObserve ring root z)
    | .active a' =>
        resetClockBankResultObserve ring root z = .inl a' := by
  cases z with
  | active b => rfl
  | retry seed => exact ⟨seed, rfl⟩
  | stop C reason => exact True.intro

/-- First recovery ends at an authentic launch or an earlier terminal. -/
theorem resetClockBankFirstLaunchTransfer {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root) (T : Nat) :
    costNumerator (resetClockBankRenewalNext ring root hsp)
      (fun x => resetClockBankRenewalLaunchCut ring root x ∨
        resetClockBankRenewalTarget ring root x)
      (.inl a) T ≤
      attemptCostNumerator (resetClockBankRetryKernel ring root hsp)
        (.active a) T := by
  refine resetClockCostLeAttemptStop
    (resetClockBankRetryKernel ring root hsp)
    (resetClockBankRenewalNext ring root hsp)
    (resetClockBankRenewalTarget ring root)
    (resetClockBankRenewalLaunchCut ring root)
    (fun x a' => x = .inl a') ?_ (.inl a) a rfl T
  intro x a' hrel hx e
  cases hrel
  have hk : (resetClockBankRetryKernel ring root hsp).step a' e =
      resetClockBankResultNode ring root
        (resetClockBankAttemptService ring root hsp a' e) := rfl
  have hn : resetClockBankRenewalNext ring root hsp (Sum.inl a') e =
      resetClockBankResultObserve ring root
        (resetClockBankAttemptService ring root hsp a' e) := rfl
  rw [hk, hn]
  have hclause := resetClockBankResultLaunchClause ring root
    (resetClockBankAttemptService ring root hsp a' e)
  revert hclause
  cases resetClockBankResultNode ring root
      (resetClockBankAttemptService ring root hsp a' e) <;>
    exact id

theorem resetClockBankFirstLaunchCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) (T : Nat) :
    costNumerator (resetClockBankRenewalNext ring root hsp)
      (fun y => resetClockBankRenewalLaunchCut ring root y ∨
        resetClockBankRenewalTarget ring root y)
      (.inl (.inr x)) T ≤ n ^ T * n := by
  exact Nat.le_trans
    (resetClockBankFirstLaunchTransfer ring root hsp (.inr x) T)
    (resetClockBankRecoveryAttemptCost ring root hsp x T)

theorem resetRenewalResetBudget (n b : Nat) :
    n + 2 * (n * (2 * b)) ≤ (4 * b + 6) * n := by
  calc
    n + 2 * (n * (2 * b)) =
        n + n * (2 * (2 * b)) := by
      congr 1
      rw [← Nat.mul_assoc, Nat.mul_comm 2 n, Nat.mul_assoc]
    _ = n * (1 + 2 * (2 * b)) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (4 * b + 6) := Nat.mul_le_mul_left n (by omega)
    _ = (4 * b + 6) * n := Nat.mul_comm _ _

/-- C.2 from the certified RESET state, stopped separately on grant
or defect. The proof first pays the initial real launch wait. -/
theorem resetClockBankResetRenewalCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root)
    (T : Nat) :
    costNumerator (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root)
      (.inl (.inr x)) T ≤
      n ^ T * ((4 * (compileAdvice q).b + 6) * n) := by
  have hh := Prob.costNumerator_stage_le
    (resetClockBankRenewalNext ring root hsp)
    (.inl (.inr x))
    (resetClockBankRenewalLaunchCut ring root)
    (resetClockBankRenewalTarget ring root)
    n (2 * (n * (2 * (compileAdvice q).b)))
    (resetClockBankFirstLaunchCost ring root hsp x)
    (by intro y hy U; obtain ⟨seed, he⟩ := hy; subst y; exact resetClockBankLaunchRenewalCost ring root hsp seed U)
    T
  exact Nat.le_trans hh (Nat.mul_le_mul_left (n ^ T)
    (resetRenewalResetBudget n (compileAdvice q).b))

/-- Repository uniform-IID expectation statement for the physical
local clean/grant/defect stopping time. No conditioning on an
exit-free event or independence between attempts is used. -/
theorem resetClockBankResetRenewalExpected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRecovery (q := q) ring root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root)
      (.inl (.inr x))
      ((((4 * (compileAdvice q).b + 6) * n : Nat) : Rat)) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (resetClockBankRenewalNext ring root hsp)
    (resetClockBankRenewalTarget ring root)
    ring.hn (.inl (.inr x))
    ((4 * (compileAdvice q).b + 6) * n)).2
  exact resetClockBankResetRenewalCost ring root hsp x


/-- Physical clean state certified by an actual returning reset. -/
def ResetClockBankClean {n q : Nat}
    (ring : DirectedRing n) (C : Config q n) (root : Fin n) : Prop :=
  Complete ring C root ∧ (C root).mode = .ARMED ∧
    (∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (C (site ring root j)).bit = false ∧
      (C (site ring root j)).tok = .E)

/-- The terminal RL service really leaves ARMED and zero/empty digits. -/
theorem resetClockBankRunSuccessClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hsuccess : resetClockBankOutcome ring root
      x.physical x.stage e = .success) :
    (((protocol q).step ring x.physical e) root).mode = .ARMED ∧
      (∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
        (((protocol q).step ring x.physical e)
          (site ring root j)).bit = false ∧
        (((protocol q).step ring x.physical e)
          (site ring root j)).tok = .E) := by
  have hfinal : e = root ∧ x.stage = .returning 1 ∧
      (((protocol q).step ring x.physical e) root).mode = .ARMED := by
    rcases resetClockBankOutcomeCases ring x.physical root hsp
        x.complete x.grantFree x.stage x.phase e with
      hl | hd | hs | hg | hw
    · rw [hsuccess] at hl
      cases hl
    · have hbad := hd.1
      rw [hsuccess] at hbad
      cases hbad
    · exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    · have hbad := hg.1
      rw [hsuccess] at hbad
      cases hbad
    · have hbad := hw.1
      rw [hsuccess] at hbad
      cases hbad
  have hreturn : ResetReturnPhysical ring x.physical root 1 := by
    have hp := x.phase
    rw [hfinal.2.1] at hp
    exact hp
  have hn : 2 ≤ n := resetTrialMinRing ring x.physical root
    x.complete (resetClockStageToTrial ring x.physical root
      x.stage x.phase)
  refine ⟨hfinal.2.2, ?_⟩
  rw [hfinal.1]
  exact resetTrialReturnTerminal ring x.physical root hn hsp
    x.complete x.grantFree hreturn

theorem resetClockBankRunSuccessComplete {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hsuccess : resetClockBankOutcome ring root
      x.physical x.stage e = .success) :
    Complete ring ((protocol q).step ring x.physical e) root := by
  have hnoDef : ¬ ResetClockBankDefectEntry
      ring x.physical root e := by
    intro hd
    have hbad : resetClockBankOutcome ring root
        x.physical x.stage e = .defect := by
      simp only [resetClockBankOutcome, if_pos hd]
    rw [hsuccess] at hbad
    cases hbad
  have hstable := resetClockBankStableOfNoDefect
    ring x.physical root e hnoDef
  intro j hj
  rw [hstable j hj]
  exact x.complete j hj

/-- Terminal labels have different physical meanings. Defect is
a property of the selected OLD edge, not an invented clean cut. -/
def ResetClockBankStopMeaning {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) :
    ResetClockBankStop → Prop
  | .clean => ResetClockBankClean ring ((protocol q).step ring C e) root
  | .grant => ¬ GrantFree ((protocol q).step ring C e) root
  | .defect => ResetClockBankDefectEntry ring C root e

/-- A classified grant outcome really violates the successor grant gate. -/
theorem resetClockBankOutcomeGrantProperty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hout : resetClockBankOutcome ring root x.physical x.stage e = .grant) :
    ¬ GrantFree ((protocol q).step ring x.physical e) root := by
  rcases resetClockBankOutcomeCases ring x.physical root hsp
      x.complete x.grantFree x.stage x.phase e with
    hl | hd | hs | hg | hw
  · rw [hout] at hl
    cases hl
  · rw [hout] at hd
    cases hd.1
  · rw [hout] at hs
    cases hs.1
  · exact hg.2
  · rw [hout] at hw
    cases hw.1

theorem resetClockBankOutcomeDefectProperty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hout : resetClockBankOutcome ring root x.physical x.stage e = .defect) :
    ResetClockBankDefectEntry ring x.physical root e := by
  rcases resetClockBankOutcomeCases ring x.physical root hsp
      x.complete x.grantFree x.stage x.phase e with
    hl | hd | hs | hg | hw
  · rw [hout] at hl
    cases hl
  · exact hd.2
  · rw [hout] at hs
    cases hs.1
  · rw [hout] at hg
    cases hg.1
  · rw [hout] at hw
    cases hw.1

/-- Every terminal label certifies its own real successor or OLD edge. -/
theorem resetClockBankServiceStopSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root) (e : Fin n)
    (D : Config q n) (reason : ResetClockBankStop)
    (hstop : resetClockBankAttemptService ring root hsp a e =
      .stop D reason) :
    ResetClockBankStopMeaning ring root
      (resetClockBankAttemptConfig ring root a) e reason := by
  cases a with
  | inl x =>
      cases hout : resetClockBankOutcome ring root x.physical x.stage e with
      | live =>
          rw [resetClockBankAttemptServiceLive ring root hsp x e hout] at hstop
          cases hstop
      | waitLoss =>
          rw [resetClockBankAttemptServiceWait ring root hsp x e hout] at hstop
          cases hstop
      | success =>
          rw [resetClockBankAttemptServiceSuccess ring root hsp x e hout] at hstop
          cases hstop
          exact ⟨resetClockBankRunSuccessComplete ring root x e hout,
            resetClockBankRunSuccessClean ring root hsp x e hout⟩
      | grant =>
          rw [resetClockBankAttemptServiceGrant ring root hsp x e hout] at hstop
          cases hstop
          exact resetClockBankOutcomeGrantProperty ring root hsp x e hout
      | defect =>
          rw [resetClockBankAttemptServiceDefect ring root hsp x e hout] at hstop
          cases hstop
          exact resetClockBankOutcomeDefectProperty ring root hsp x e hout
  | inr x =>
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankAttemptServiceRecoverDefect ring root hsp x e hd] at hstop
        cases hstop
        exact hd
      · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
        · by_cases he : e = root
          · obtain ⟨seed, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverRetry
                ring root hsp x e hd hg he
            rw [hs] at hstop
            cases hstop
          · obtain ⟨y, hs, hv⟩ :=
              resetClockBankAttemptServiceRecoverContinue
                ring root hsp x e hd hg he
            rw [hs] at hstop
            cases hstop
        · rw [resetClockBankAttemptServiceRecoverGrant ring root hsp x e hd hg] at hstop
          cases hstop
          exact hg

/-- Direct entry point from the previously certified waitLoss edge.
It includes every real recovery edge before the next launch. -/
theorem resetClockBankWaitLossRenewalExpected {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankRun (q := q) ring root) (e : Fin n)
    (hwait : resetClockBankOutcome ring root
      x.physical x.stage e = .waitLoss) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root)
      (.inl (.inr (resetClockBankRunRecovery ring root hsp x e hwait)))
      ((((4 * (compileAdvice q).b + 6) * n : Nat) : Rat)) := by
  exact resetClockBankResetRenewalExpected ring root hsp
    (resetClockBankRunRecovery ring root hsp x e hwait)

end Counter
end L3
