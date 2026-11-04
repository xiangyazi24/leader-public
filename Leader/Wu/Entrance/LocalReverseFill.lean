import Leader.Wu.Entrance.WindowLocality
import Leader.Wu.Birth.CheckChainPerBlock
import Leader.Wu.Splice.MatcherMass

/-!
# Local reverse-fill certificates and their original-word mass

Packages the direct local reverse-fill obligations.

An interval is a nonempty cyclic arc of at most n distinct physical cells.
The requested word uses the original full-ring R1 step. Every request must
be internal to the interval, and success is a leader inside the interval or
an exact ready window entirely inside it, at some prefix.

The minimal certificate makes no assertion about GEN ancestry, bit freezing,
preparation, or a reverse-delivery history. A stronger routing construction
can supply this certificate by proving a physical prefix hit.

The mass proof selects a shortest successful requested prefix, applies the
ordered touching-edge matcher, transfers the hit by full-record locality,
and pads the resulting stopped event. The entrance theorem composes on
Unfinished = Leaderless and not ReadyWindow; no persistence of Routable or
of readiness after a hit is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6LocalReverseFill

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open BirthCheckChainR1PerBlock BirthCheckChainR1Mass
open B6WindowLocality B9OrderedWindowMatcher
open BirthTwoStageEscape BirthLeaderlessBirthMassRenewal
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open ThreePortSerialCount B9SpliceTripleHitWords

-- All physical reasoning below uses the exported pair-locality theorem.
-- Do not expand the complete protocol row during count elaboration.
attribute [local irreducible] BirthCheckPermitRepairLeaf.step1

variable {n ψ κ τ : Nat}

abbrev Config (n ψ κ τ : Nat) :=
  BirthCheckPermitRepairLeaf.FC n ψ κ τ

/-- The cells are cell ring first k, for 0 <= k < size. -/
structure Interval (ring : DirectedRing n) where
  first : Fin n
  size : Nat
  nonempty : 0 < size
  fits : size ≤ n

/-- The whole ring is an allowed interval, not an exceptional dynamics. -/
def wholeInterval (ring : DirectedRing n) (s : Fin n) : Interval ring where
  first := s
  size := n
  nonempty := ring.hn
  fits := Nat.le_refl n

/-- Membership in the actual cyclic arc. -/
def support {ring : DirectedRing n} (I : Interval ring) : Fin n → Bool :=
  BirthCheckChainR1Mass.window ring I.first I.size

/-- The size bound rules out repeated cells, including in the whole-ring case. -/
theorem interval_cells_injective {ring : DirectedRing n} (I : Interval ring)
    (a b : Fin I.size)
    (hab : cell ring I.first a.val = cell ring I.first b.val) : a = b := by
  apply Fin.ext
  by_cases he : a.val = b.val
  · exact he
  · exact (cell_ne ring I.first
      (Nat.lt_of_lt_of_le a.isLt I.fits)
      (Nat.lt_of_lt_of_le b.isLt I.fits) he hab).elim

theorem support_cell {ring : DirectedRing n} (I : Interval ring)
    {k : Nat} (hk : k < I.size) :
    support I (cell ring I.first k) = true := by
  exact window_cell ring I.first hk

/-- This counts all incident edges, not only the distinct requests. -/
theorem touchCount_support_le {ring : DirectedRing n} (I : Interval ring) :
    touchCount (touchOf ring (support I)) ≤ I.size + 1 := by
  exact touchCount_window_le (ψ := I.size) ring I.first

/-- Both endpoints of the directed scheduler edge lie in the interval. -/
def internal {ring : DirectedRing n} (I : Interval ring) (e : Fin n) : Prop :=
  internalOf ring (support I) e = true

theorem internal_iff {ring : DirectedRing n} (I : Interval ring) (e : Fin n) :
    internal I e ↔
      support I e = true ∧ support I (ring.rightNeighbor e) = true := by
  simp only [internal, internalOf, Bool.and_eq_true]

theorem internal_touch {ring : DirectedRing n} (I : Interval ring) (e : Fin n)
    (he : internal I e) : touchOf ring (support I) e = true := by
  have hi := (internal_iff I e).mp he
  simp [touchOf, hi.1]

def InternalWord {ring : DirectedRing n} (I : Interval ring)
    (w : List (Fin n)) : Prop :=
  ∀ e ∈ w, internal I e

/-- This is the actual R1 run, with no clipping or exterior replacement. -/
def runR (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (w : List (Fin n)) (C : Config n ψ κ τ) : Config n ψ κ τ :=
  w.foldl (step1 hψ h2 ring) C

def ContainsTarget (ring : DirectedRing n) (I : Interval ring)
    (s : Fin n) (width : Nat) : Prop :=
  ∀ k : Fin width, support I (cell ring s k.val) = true

def ReadyInside (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∃ s : Fin n, ContainsTarget ring I s ψ ∧
    ∀ k : Fin ψ, ReadyCell k.val (C (cell ring s k.val))

def HitInside (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  (∃ i : Fin n, support I i = true ∧ (C i).core.core.leader = true) ∨
    ReadyInside ring I C

/-- Minimal physical certificate: internal requests and a successful prefix. -/
def LocalReverseFill (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (I : Interval ring)
    (w : List (Fin n)) (C : Config n ψ κ τ) : Prop :=
  InternalWord I w ∧
    ∃ p : List (Fin n), p <+: w ∧
      HitInside ring I (runR hψ h2 ring p C)

/-- Leaving this class is already a first-stage success. -/
def Unfinished (ring : DirectedRing n) (C : Config n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ∧ ¬ ReadyWindow ring C

theorem readyInside_readyWindow (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) (h : ReadyInside ring I C) : ReadyWindow ring C := by
  rcases h with ⟨s, _, hs⟩
  exact ⟨s, fun k hk => hs ⟨k, hk⟩⟩

/-- A hit is determined by the complete records on its interval. -/
theorem hitInside_of_agree (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : HitInside ring I C) : HitInside ring I D := by
  rcases h with ⟨i, hi, hlead⟩ | ⟨s, hs, hready⟩
  · left
    refine ⟨i, hi, ?_⟩
    rw [← hCD i hi]
    exact hlead
  · right
    refine ⟨s, hs, ?_⟩
    intro k
    rw [← hCD (cell ring s k.val) (hs k)]
    exact hready k

theorem hitInside_not_unfinished (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) (h : HitInside ring I C) : ¬ Unfinished ring C := by
  intro hU
  rcases h with ⟨i, _, hlead⟩ | hready
  · have hf := hU.1 i
    rw [hlead] at hf
    cases hf
  · exact hU.2 (readyInside_readyWindow ring I C hready)

private theorem prefix_length_le_local {α : Type} {p w : List α}
    (hp : p <+: w) : p.length ≤ w.length := by
  rcases hp with ⟨v, rfl⟩
  simp only [List.length_append]
  omega

theorem internalWord_prefix {ring : DirectedRing n} (I : Interval ring)
    {p w : List (Fin n)} (hw : InternalWord I w) (hp : p <+: w) :
    InternalWord I p := by
  rcases hp with ⟨v, rfl⟩
  intro e he
  exact hw e (List.mem_append.mpr (Or.inl he))

theorem localReverseFill_hit_prefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (h : LocalReverseFill hψ h2 ring I w C) :
    ∃ p : List (Fin n), p <+: w ∧ InternalWord I p ∧
      HitInside ring I (runR hψ h2 ring p C) := by
  rcases h with ⟨hw, p, hp, hhit⟩
  exact ⟨p, hp, internalWord_prefix I hw hp, hhit⟩

/-- Elementary bounded minimization, avoiding a library-specific find API. -/
private theorem least_nat_below (P : Nat → Prop) :
    ∀ N : Nat, (∃ k, k ≤ N ∧ P k) →
      ∃ k, P k ∧ ∀ r, P r → k ≤ r := by
  classical
  intro N
  induction N with
  | zero =>
      rintro ⟨k, hk, hPk⟩
      have hk0 : k = 0 := by omega
      subst k
      exact ⟨0, hPk, fun r _ => Nat.zero_le r⟩
  | succ N ih =>
      intro hex
      by_cases he : ∃ k, k ≤ N ∧ P k
      · exact ih he
      · rcases hex with ⟨k, hk, hPk⟩
        refine ⟨k, hPk, ?_⟩
        intro r hPr
        by_cases hkr : k ≤ r
        · exact hkr
        · have hrN : r ≤ N := by omega
          exact (he ⟨r, hrN, hPr⟩).elim

/-- Select the shortest successful prefix of the requested word. -/
theorem localReverseFill_shortest_prefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (h : LocalReverseFill hψ h2 ring I w C) :
    ∃ p : List (Fin n), p <+: w ∧ InternalWord I p ∧
      HitInside ring I (runR hψ h2 ring p C) ∧
      ∀ q : List (Fin n), q <+: w →
        HitInside ring I (runR hψ h2 ring q C) → p.length ≤ q.length := by
  rcases h with ⟨hw, q, hq, hqhit⟩
  let P : Nat → Prop := fun r =>
    ∃ p : List (Fin n), p <+: w ∧
      HitInside ring I (runR hψ h2 ring p C) ∧ p.length = r
  have hex : ∃ r, r ≤ w.length ∧ P r :=
    ⟨q.length, prefix_length_le_local hq, q, hq, hqhit, rfl⟩
  rcases least_nat_below P w.length hex with ⟨r, hr, hmin⟩
  rcases hr with ⟨p, hp, hhit, hlen⟩
  refine ⟨p, hp, internalWord_prefix I hw hp, hhit, ?_⟩
  intro v hv hvhit
  rw [hlen]
  exact hmin v.length ⟨v, hv, hvhit, rfl⟩

/-- The certificate is local in the initial complete interval records. -/
theorem localReverseFill_of_agree
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C D : Config n ψ κ τ)
    (hCD : ∀ i, support I i = true → C i = D i)
    (h : LocalReverseFill hψ h2 ring I w C) :
    LocalReverseFill hψ h2 ring I w D := by
  rcases h with ⟨hw, p, hp, hhit⟩
  have hi := internalWord_prefix I hw hp
  have hagree := B6WindowLocality.run_agree
    (step1_pairLocal (kappa := κ) (tau := τ) hψ h2 ring)
    (support I) p C D hCD (fun e he _ => hi e he)
  exact ⟨hw, p, hp,
    hitInside_of_agree ring I (runR hψ h2 ring p C)
      (runR hψ h2 ring p D) hagree hhit⟩

/-! ## Generic stopped-event bookkeeping -/

private theorem avoidAlong_iff_alive_complement {S : Type}
    (step : S → Fin n → S) (Good R : S → Prop)
    (C : S) (w : List (Fin n)) :
    AvoidAlong step Good R C w ↔
      AliveAlong step (fun D => Good D ∧ ¬ R D) C w := by
  induction w generalizing C with
  | nil => rfl
  | cons e w ih =>
      change ((Good C ∧ ¬ R C) ∧ AvoidAlong step Good R (step C e) w) ↔
        ((Good C ∧ ¬ R C) ∧
          AliveAlong step (fun D => Good D ∧ ¬ R D) (step C e) w)
      constructor
      · intro h
        exact ⟨h.1, (ih (step C e)).mp h.2⟩
      · intro h
        exact ⟨h.1, (ih (step C e)).mpr h.2⟩

theorem avoidCount_eq_alive_complement {S : Type}
    (step : S → Fin n → S) (Good R : S → Prop) (C : S) (T : Nat) :
    avoidCount step Good R C T =
      aliveCount step (fun D => Good D ∧ ¬ R D) C T := by
  unfold avoidCount aliveCount
  have hbits : avoidBit step Good R C =
      aliveBit step (fun D => Good D ∧ ¬ R D) C := by
    funext w
    classical
    unfold avoidBit aliveBit
    rw [avoidAlong_iff_alive_complement]
  rw [hbits]

theorem avoidCount_eq_alive_unfinished
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) (T : Nat) :
    avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C T =
      aliveCount (step1 hψ h2 ring) (Unfinished ring) C T := by
  exact avoidCount_eq_alive_complement (step1 hψ h2 ring)
    BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C T

private theorem avoidAlong_mono_good {S : Type}
    (step : S → Fin n → S) (Good Good' R : S → Prop)
    (hGood : ∀ D, Good D → Good' D) (C : S) (w : List (Fin n)) :
    AvoidAlong step Good R C w → AvoidAlong step Good' R C w := by
  induction w generalizing C with
  | nil =>
      intro h
      exact ⟨hGood C h.1, h.2⟩
  | cons e w ih =>
      intro h
      exact ⟨⟨hGood C h.1.1, h.1.2⟩, ih (step C e) h.2⟩

/-- Strengthening the alive class only decreases the avoidance numerator. -/
theorem avoidCount_mono_good {S : Type}
    (step : S → Fin n → S) (Good Good' R : S → Prop)
    (hGood : ∀ D, Good D → Good' D) (C : S) (T : Nat) :
    avoidCount step Good R C T ≤ avoidCount step Good' R C T := by
  unfold avoidCount
  apply B9SpliceMatcherMass.wordSum_mono
  intro w
  classical
  unfold avoidBit
  by_cases h : AvoidAlong step Good R C w
  · have h' := avoidAlong_mono_good step Good Good' R hGood C w h
    simp [h, h']
  · simp [h]

private theorem power_mono_exp (b r s : Nat) (hb : 1 ≤ b) (hrs : r ≤ s) :
    b ^ r ≤ b ^ s := by
  have he : r + (s - r) = s := by omega
  have hd : 1 ≤ b ^ (s - r) := Nat.pow_pos (by omega)
  calc
    b ^ r ≤ b ^ r * b ^ (s - r) := Nat.le_mul_of_pos_right _ hd
    _ = b ^ s := by rw [← Nat.pow_add, he]

private theorem disjoint_escape (A B N Q : Nat)
    (hpair : A + B ≤ N) (hmass : N ≤ Q * B) :
    Q * A ≤ (Q - 1) * N := by
  have hs : Q * A + Q * B ≤ Q * N := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left Q hpair
  rw [Nat.sub_one_mul]
  omega

private theorem alive_mass_pad {S : Type}
    (step : S → Fin n → S) (Good : S → Prop) (C : S)
    (T U Q : Nat) (hTU : T ≤ U)
    (hbase : Q * aliveCount step Good C T ≤ (Q - 1) * n ^ T) :
    Q * aliveCount step Good C U ≤ (Q - 1) * n ^ U := by
  have hsum : T + (U - T) = U := by omega
  have hp := BirthTwoStageEscape.alive_pad step Good (U - T) T C
  rw [hsum] at hp
  calc
    Q * aliveCount step Good C U
        ≤ Q * (aliveCount step Good C T * n ^ (U - T)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good C T) * n ^ (U - T) := by
      rw [Nat.mul_assoc]
    _ ≤ ((Q - 1) * n ^ T) * n ^ (U - T) :=
      Nat.mul_le_mul_right _ hbase
    _ = (Q - 1) * n ^ U := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

/-! ## Matcher success is disjoint from remaining unfinished -/

theorem matcher_success_not_alive
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (req : List (Fin n)) (C : Config n ψ κ τ)
    (hne : req ≠ []) (hint : InternalWord I req)
    (hhit : HitInside ring I (runR hψ h2 ring req C))
    (u : List (Fin n))
    (hs : runNode (ordStep (touchOf ring (support I))) (.active req) u =
      StopNode.success) :
    aliveBit (step1 hψ h2 ring) (Unfinished ring) C u = 0 := by
  classical
  rcases B6WindowLocality.success_prefix_agrees
      (step1_pairLocal (kappa := κ) (tau := τ) hψ h2 ring)
      (support I) req hne (fun e he => hint e he) u hs C with
    ⟨p, hp, hagree⟩
  have hpHit : HitInside ring I (runR hψ h2 ring p C) :=
    hitInside_of_agree ring I (runR hψ h2 ring req C)
      (runR hψ h2 ring p C) (fun i hi => (hagree i hi).symm) hhit
  unfold aliveBit
  apply if_neg
  intro halive
  rcases hp with ⟨v, rfl⟩
  have hsplit := (aliveAlong_append (step1 hψ h2 ring)
    (Unfinished ring) C p v).mp halive
  have hU : Unfinished ring (p.foldl (step1 hψ h2 ring) C) :=
    aliveAlong_good hsplit.2
  exact hitInside_not_unfinished ring I (runR hψ h2 ring p C) hpHit hU

/-- Use the final coarse denominator already at the shorter hit horizon. -/
private theorem request_hit_alive_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (req : List (Fin n)) (C : Config n ψ κ τ)
    (L M : Nat) (hM : 1 ≤ M) (hlen : req.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hne : req ≠ []) (hint : InternalWord I req)
    (hhit : HitInside ring I (runR hψ h2 ring req C)) :
    (4 * M) ^ L * aliveCount (step1 hψ h2 ring) (Unfinished ring)
        C (2 * n * req.length) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * req.length) := by
  classical
  let touch : Fin n → Bool := touchOf ring (support I)
  let st : Config n ψ κ τ → Fin n → Config n ψ κ τ := step1 hψ h2 ring
  let H := 2 * n * req.length
  let A := aliveCount st (Unfinished ring) C H
  let B := wordSum n H (fun u =>
    successWeight (runStopped (ordStep touch) (.active req) u))
  let N := n ^ H
  let Q := (4 * M) ^ L
  have hmass := B9OrderedWindowMatcher.ordered_mass touch req hne
    (fun e he => internal_touch I e (hint e he))
  rw [← B9SpliceMatcherMass.wordSum_success_eq_successCount] at hmass
  change 3 ^ req.length * N ≤ (4 * touchCount touch) ^ req.length * B at hmass
  have hpair : A + B ≤ N := by
    change wordSum n H (aliveBit st (Unfinished ring) C) +
      wordSum n H (fun u =>
        successWeight (runStopped (ordStep touch) (.active req) u)) ≤ n ^ H
    apply BirthCheckChainR1Mass.wordSum_pair_le
    intro u
    by_cases hsu : runStopped (ordStep touch) (.active req) u = StopNode.success
    · have hs : runNode (ordStep touch) (.active req) u = StopNode.success := by
        rw [B9SpliceMatcherMass.runNode_eq_runStopped]
        exact hsu
      have hz := matcher_success_not_alive hψ h2 ring I req C hne hint hhit u hs
      change aliveBit st (Unfinished ring) C u = 0 at hz
      rw [hz, hsu]
      show 0 + 1 ≤ 1
      exact Nat.le_refl 1
    · have hzero : successWeight (runStopped (ordStep touch) (.active req) u) = 0 := by
        cases hu : runStopped (ordStep touch) (.active req) u with
        | active x => rfl
        | success => exact (hsu hu).elim
        | failure => rfl
      rw [hzero, Nat.add_zero]
      exact aliveBit_le_one st (Unfinished ring) C u
  have hbase : 4 * touchCount touch ≤ 4 * M := Nat.mul_le_mul_left 4 ht
  have hcoef : (4 * touchCount touch) ^ req.length ≤ Q :=
    Nat.le_trans (Nat.pow_le_pow_left hbase req.length)
      (power_mono_exp (4 * M) req.length L (by omega) hlen)
  have hthree : 1 ≤ 3 ^ req.length := Nat.pow_pos (by decide : 0 < 3)
  have hN : N ≤ 3 ^ req.length * N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N hthree
  have hscale : N ≤ Q * B :=
    Nat.le_trans hN (Nat.le_trans hmass (Nat.mul_le_mul_right B hcoef))
  change Q * A ≤ (Q - 1) * N
  exact disjoint_escape A B N Q hpair hscale

/-- The original-word mass of any bounded local physical hit certificate. -/
theorem localReverseFill_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) (C : Config n ψ κ τ)
    (L M : Nat) (hM : 1 ≤ M) (hL : w.length ≤ L)
    (ht : touchCount (touchOf ring (support I)) ≤ M)
    (hfill : LocalReverseFill hψ h2 ring I w C) :
    (4 * M) ^ L * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring)
        C (2 * n * L) ≤
      ((4 * M) ^ L - 1) * n ^ (2 * n * L) := by
  rcases localReverseFill_shortest_prefix hψ h2 ring I w C hfill with
    ⟨p, hp, hint, hhit, _⟩
  have hpL : p.length ≤ L := Nat.le_trans (prefix_length_le_local hp) hL
  rw [avoidCount_eq_alive_unfinished]
  by_cases hp0 : p = []
  · have hC : HitInside ring I C := by
      simpa only [hp0, runR, List.foldl_nil] using hhit
    rw [BirthTwoStageEscape.aliveCount_not_good (step1 hψ h2 ring)
      (Unfinished ring) C (hitInside_not_unfinished ring I C hC)
      (2 * n * L), Nat.mul_zero]
    exact Nat.zero_le _
  · have hm := request_hit_alive_mass hψ h2 ring I p C L M
      hM hpL ht hp0 hint hhit
    exact alive_mass_pad (step1 hψ h2 ring) (Unfinished ring) C
      (2 * n * p.length) (2 * n * L) ((4 * M) ^ L)
      (Nat.mul_le_mul_left (2 * n) hpL) hm

/-! ## Uniform entrance and the exact ready-window h1 -/

/-- I and w are chosen from the reached configuration, before its new block. -/
def Routable (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L M : Nat) (C : Config n ψ κ τ) : Prop :=
  ∃ I : Interval ring, ∃ w : List (Fin n),
    LocalReverseFill hψ h2 ring I w C ∧ w.length ≤ L ∧
      touchCount (touchOf ring (support I)) ≤ M

/-- A first-hit entrance contract, not an endpoint-retention contract. -/
def UniformRouteEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L M B0 Q0 : Nat) : Prop :=
  ∀ C : Config n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
    Q0 * avoidCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (Routable hψ h2 ring L M) C B0 ≤
      (Q0 - 1) * n ^ B0

/-- Export exactly h1 with B1 = B0 + 2*n*L and Q1 = Q0*(4*M)^L. -/
theorem h1_of_route_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L M B0 Q0 : Nat) (hM : 1 ≤ M) (hQ0 : 1 ≤ Q0)
    (hentr : UniformRouteEntrance (κ := κ) (τ := τ)
      hψ h2 ring L M B0 Q0) :
    ∀ C : Config n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      (Q0 * (4 * M) ^ L) * avoidCount (step1 hψ h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring)
          C (B0 + 2 * n * L) ≤
        (Q0 * (4 * M) ^ L - 1) * n ^ (B0 + 2 * n * L) := by
  have hQr : 1 ≤ (4 * M) ^ L := Nat.pow_pos (by omega)
  have hfirst : ∀ D : Config n ψ κ τ, Unfinished ring D →
      Q0 * avoidCount (step1 hψ h2 ring) (Unfinished ring)
          (Routable hψ h2 ring L M) D B0 ≤ (Q0 - 1) * n ^ B0 := by
    intro D hD
    have hmono := avoidCount_mono_good (step1 hψ h2 ring)
      (Unfinished ring) BirthShortDoneTerminalFirstHit.Leaderless
      (Routable hψ h2 ring L M) (fun E hE => hE.1) D B0
    exact Nat.le_trans (Nat.mul_le_mul_left Q0 hmono) (hentr D hD.1)
  have hsecond : ∀ D : Config n ψ κ τ, Unfinished ring D →
      Routable hψ h2 ring L M D →
      (4 * M) ^ L * aliveCount (step1 hψ h2 ring) (Unfinished ring)
          D (2 * n * L) ≤
        ((4 * M) ^ L - 1) * n ^ (2 * n * L) := by
    intro D _ hD
    rcases hD with ⟨I, w, hfill, hlen, ht⟩
    have hm := localReverseFill_mass hψ h2 ring I w D L M hM hlen ht hfill
    rw [avoidCount_eq_alive_unfinished] at hm
    exact hm
  have htwo := BirthTwoStageEscape.two_stage_escape
    (step1 (kappa := κ) (tau := τ) hψ h2 ring)
    (Unfinished ring) (Routable hψ h2 ring L M)
    B0 (2 * n * L) Q0 ((4 * M) ^ L) hQ0 hQr hfirst hsecond
  intro C hC
  rw [avoidCount_eq_alive_unfinished]
  by_cases hready : ReadyWindow ring C
  · have hbad : ¬ Unfinished ring C := fun h => h.2 hready
    rw [BirthTwoStageEscape.aliveCount_not_good (step1 hψ h2 ring)
      (Unfinished ring) C hbad (B0 + 2 * n * L), Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC, hready⟩

/-- Plan-name alias, with the task's minimal L,M-only Routable interface. -/
theorem ready_window_mass_of_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L M B0 Q0 : Nat) (hM : 1 ≤ M) (hQ0 : 1 ≤ Q0)
    (hentr : UniformRouteEntrance (κ := κ) (τ := τ)
      hψ h2 ring L M B0 Q0) :
    ∀ C : Config n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      (Q0 * (4 * M) ^ L) * avoidCount (step1 hψ h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring)
          C (B0 + 2 * n * L) ≤
        (Q0 * (4 * M) ^ L - 1) * n ^ (B0 + 2 * n * L) := by
  exact h1_of_route_entrance hψ h2 ring L M B0 Q0 hM hQ0 hentr

end B6LocalReverseFill

