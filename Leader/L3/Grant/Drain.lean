import Leader.L3.NativeBirth
import Leader.L3.NativeSector
import Leader.L3.Purification
import Leader.L3.ProbRenewal

namespace L3

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
Grant-drain no-new-grant reference, for tokens.tex, lem:grant-drain.

Scaffold.  This deliberately does not assert
the full 109/3 bound: the cited paper uses birth/death charges,
a stopping-time dichotomy, and simultaneous label clocks, not one
globally nonincreasing warm-rank.

The hostile request bit is chosen from the complete OLD state plus
the revealed current edge.  An arbitrary auxiliary state and the
actual edge history are retained, so strategies need not be Markov
on native/request/grant fields alone.
-/

/-- The three source selectors, in their literal priority order. -/
inductive GrantDrainFire
  | none
  | leftLocal
  | rightLocal
  | cross
  deriving BEq, DecidableEq, Repr

/-- Entire reference configuration, including an adversary-owned
    ghost/scratch coordinate and the revealed edge history. -/
structure GrantDrainState (n : Nat) (Scratch : Type) where
  native : Fin n → CertNative
  request : Fin n → Bool
  grant : Fin n → Bool
  scratch : Scratch
  history : List (Fin n)

/-- The no-new-grant target. -/
def GrantFree {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) : Prop :=
  ∀ i : Fin n, s.grant i = false

/-- FIRE's post-E test: follower, no bullet. -/
def grantDrainEligible {n : Nat}
    (N : Fin n → CertNative) (z : Fin n) : Bool :=
  !(N z).l && ((N z).b.val == 0)

/-- The old-token F0/F1/F2 selector with post-E eligibility.
    No fresh request is read by this selector. -/
def grantDrainSelect {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) : GrantDrainFire :=
  let y := ring.rightNeighbor e
  let post := nativeE ring s.native e
  if s.request e && s.grant e && grantDrainEligible post e then
    .leftLocal
  else if s.request y && s.grant y && grantDrainEligible post y then
    .rightLocal
  else if s.request e && s.grant y && grantDrainEligible post e then
    .cross
  else .none

/-- Apply native E, then exactly the canonical birth selected by
    an OLD grant.  Every successful selector consumes one OLD grant
    in the token owner below. -/
def grantDrainNativeNext {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) : Fin n → CertNative :=
  let post := nativeE ring s.native e
  match grantDrainSelect ring s e with
  | .none => post
  | .leftLocal => canonicalBirth post e
  | .rightLocal => canonicalBirth post (ring.rightNeighbor e)
  | .cross => canonicalBirth post e

/-- Two-site token owner, no new grant producer.  The final native
    leader bits are supplied AFTER canonical birth.  T0 consumption,
    T1 sinks, responder-only fresh request, OLD HOLD, clockwise
    request and counterclockwise grant transport, final sinks are in
    the same order as Base.tokenStep. -/
def grantDrainTokenRow
    (rx gx ry gy finalLX finalLY freshReq : Bool)
    (fire : GrantDrainFire) : TokPair × TokPair := Id.run do
  let consumeRX := fire == .leftLocal || fire == .cross
  let consumeRY := fire == .rightLocal
  let consumeGX := fire == .leftLocal
  let consumeGY := fire == .rightLocal || fire == .cross
  let fireX := fire == .leftLocal || fire == .cross
  let fireY := fire == .rightLocal
  let mut outRX := if consumeRX then false else rx
  let mut outGX := if consumeGX then false else gx
  let mut outRY := if consumeRY then false else ry
  let mut outGY := if consumeGY then false else gy
  let mut usedRX := consumeRX
  let mut usedGX := consumeGX
  let mut usedRY := consumeRY
  let mut usedGY := consumeGY
  if finalLX then
    outRX := false
    outGX := false
    usedRX := true
    usedGX := true
  if finalLY then
    outRY := false
    outGY := false
    usedRY := true
    usedGY := true
  if finalLY && rx then
    outRX := false
    usedRX := true
  if finalLX && gy then
    outGY := false
    usedGY := true
  if freshReq && !finalLY && !usedRY then
    outRY := true
  let holdX := rx && gx && !fireX && !usedRX && !usedGX
  let holdY := ry && gy && !fireY && !usedRY && !usedGY
  if holdX then
    outRX := true
    outGX := true
  if holdY then
    outRY := true
    outGY := true
  if rx && !usedRX && !holdX && !finalLY then
    outRX := false
    if !usedRY then outRY := true
  if gy && !usedGY && !holdY && !finalLX then
    outGY := false
    if !usedGX then outGX := true
  if finalLX then
    outRX := false
    outGX := false
  if finalLY then
    outRY := false
    outGY := false
  return ({ req := outRX, grant := outGX },
          { req := outRY, grant := outGY })

/-- A local, literal and finite no-cloning check.  The new responder
    request may be chosen adversarially, including on this service.
    It cannot create a grant. -/
theorem grantDrainTokenRow_noncloning
    (rx gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire) :
    (if (grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant
       then 1 else 0) +
    (if (grantDrainTokenRow rx gx ry gy lx ly fresh fire).2.grant
       then 1 else 0) ≤
    (if gx then 1 else 0) + (if gy then 1 else 0) := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> decide

private theorem grantDrainTokenRow_empty
    (rx ry lx ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx false ry false lx ly fresh fire).1.grant = false ∧
    (grantDrainTokenRow rx false ry false lx ly fresh fire).2.grant = false := by
  cases rx <;> cases ry <;> cases lx <;> cases ly <;>
    cases fresh <;> cases fire <;> decide

/-- One physical IID edge, with a hostile response chosen using the
    OLD full state and revealed edge.  History and arbitrary scratch
    are framed except for the caller's adapted update. -/
def grantDrainStep {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    GrantDrainState n Scratch :=
  let y := ring.rightNeighbor e
  let N' := grantDrainNativeNext ring s e
  let fire := grantDrainSelect ring s e
  let t := grantDrainTokenRow
    (s.request e) (s.grant e) (s.request y) (s.grant y)
    (N' e).l (N' y).l (freshRequest s e) fire
  { native := N'
    request := fun i =>
      if i = e then t.1.req
      else if i = y then t.2.req else s.request i
    grant := fun i =>
      if i = e then t.1.grant
      else if i = y then t.2.grant else s.grant i
    scratch := updateScratch s e
    history := e :: s.history }

/-- Native E plus canonical birth preserves the rooted peaceful domain. -/
private theorem grantDrainBirth_preserves_PPlus {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (z : Fin n) (h : PPlus ring N) :
    PPlus ring (canonicalBirth N z) :=
  ⟨canonicalBirth_has_leader N z,
   canonicalBirth_preserves_P ring N z h.2⟩

theorem grantDrainNativeNext_preserves_PPlus
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (h : PPlus ring s.native) :
    PPlus ring (grantDrainNativeNext ring s e) := by
  have hE := nativeE_preserves_PPlus hn ring s.native e h
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simpa [grantDrainNativeNext, hf] using
        grantDrainBirth_preserves_PPlus ring
          (nativeE ring s.native e) e hE
  | rightLocal =>
      simpa [grantDrainNativeNext, hf] using
        grantDrainBirth_preserves_PPlus ring
          (nativeE ring s.native e) (ring.rightNeighbor e) hE
  | cross =>
      simpa [grantDrainNativeNext, hf] using
        grantDrainBirth_preserves_PPlus ring
          (nativeE ring s.native e) e hE

theorem grantDrainStep_preserves_PPlus
    {n : Nat} {Scratch : Type}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (h : PPlus ring s.native) :
    PPlus ring (grantDrainStep ring freshRequest updateScratch s e).native := by
  change PPlus ring (grantDrainNativeNext ring s e)
  exact grantDrainNativeNext_preserves_PPlus hn ring s e h

/-- No birth is selected if no physical grant exists at this cut. -/
theorem grantDrainSelect_empty {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (h : GrantFree s) :
    grantDrainSelect ring s e = .none := by
  simp [grantDrainSelect, h e, h (ring.rightNeighbor e)]

theorem grantDrainNative_empty {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (h : GrantFree s) :
    grantDrainNativeNext ring s e = nativeE ring s.native e := by
  simp [grantDrainNativeNext, grantDrainSelect_empty ring s e h]

/-- Inherited grants are never manufactured after complete extinction.
    This also proves that GrantFree is an all-edge closed target for
    the reference, regardless of the hostile policy. -/
theorem grantDrainStep_preserves_GrantFree
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (h : GrantFree s) :
    GrantFree (grantDrainStep ring freshRequest updateScratch s e) := by
  intro i
  let y := ring.rightNeighbor e
  let N' := grantDrainNativeNext ring s e
  let fire := grantDrainSelect ring s e
  let t := grantDrainTokenRow
    (s.request e) (s.grant e) (s.request y) (s.grant y)
    (N' e).l (N' y).l (freshRequest s e) fire
  have ht : t.1.grant = false ∧ t.2.grant = false := by
    dsimp [t]
    rw [h e, h y]
    exact grantDrainTokenRow_empty (s.request e) (s.request y)
      (N' e).l (N' y).l (freshRequest s e) fire
  change (if i = e then t.1.grant
          else if i = y then t.2.grant
          else s.grant i) = false
  by_cases he : i = e
  · simpa only [if_pos he] using ht.1
  · by_cases hy : i = y
    · simpa only [if_neg he, if_pos hy] using ht.2
    · simpa only [if_neg he, if_neg hy] using h i

/-- There are at most n occupied physical grant slots at any cut. -/
theorem grantDrain_slots_le {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) :
    (List.ofFn (fun i : Fin n => if s.grant i then 1 else 0)).sum ≤ n := by
  calc
    (List.ofFn (fun i : Fin n => if s.grant i then 1 else 0)).sum ≤
        (List.ofFn (fun _ : Fin n => 1)).sum :=
      ofFn_sum_le _ _ (fun i => by cases s.grant i <;> decide)
    _ = n := by simp [ofFn_sum_const]

/-! ## Native-sector geometry and the actual D.6 warm rank -/

/-- Clockwise distance from the last leader to g, obtained by scanning
    counterclockwise from g.  This is a proof observer, not a stored byte. -/
def grantDrainLeftLeaderDistance {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (g : Fin n) : Nat :=
  let distances := (List.range n).map (fun k => k + 1)
  (distances.find? (fun d => (N (PPL.shiftLeft ring g d)).l)).getD n

/-- Nearest bullet behind the current grant, up to and INCLUDING the
    preceding leader's own site (distance d); its value is its distance
    behind the grant.  A ready leader's live or dummy firing leaves its
    bullet on the leader site, and the paper's D.6 counts that bullet
    as the left bullet ("a ready leader must dummy-fire, creating a left
    bullet").  Scanning only 1..d-1 missed it, and the
    resulting rank rose from 1+d to 2d-f+1 on a no-FIRE edge. -/
def grantDrainLeftBulletDistance {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (g : Fin n) (d : Nat) : Option Nat :=
  let distances := (List.range d).map (fun k => k + 1)
  distances.find? (fun p =>
    (N (PPL.shiftLeft ring g p)).b.val != 0)

/-- Number of consecutive signal-one sites ending at g, minus one.
    In the paper this is f in D.6. -/
def grantDrainTerminalRun {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (g : Fin n) (d : Nat) : Nat :=
  ((List.range d).takeWhile
      (fun k => (N (PPL.shiftLeft ring g k)).sg)).length - 1

/-- The paper's D.6 local warm grant rank, with the preceding-leader
    and left-bullet geometry recomputed from the ACTUAL native state.
    Meaningful on a clean-sector, unheld, bullet-free, signal-one
    follower grant.  No global monotonicity is claimed here. -/
def grantDrainWarmRank {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (g : Fin n) : Nat :=
  let d := grantDrainLeftLeaderDistance ring N g
  let f := grantDrainTerminalRun ring N g d
  match grantDrainLeftBulletDistance ring N g d with
  | some p => p + 2 * (p - (f + 1))
  | none =>
      if (N (PPL.shiftLeft ring g d)).sg
      then 1 + d else 2 * d - f + 1

/-! ## Exact PAPER-GAP candidate against a globally nonincreasing
    warm-rank claim (not against the audited paper's charged proof). -/

private def grantDrainWitnessRing : DirectedRing 8 := ⟨by decide⟩

private def grantDrainWitnessNative (i : Fin 8) : CertNative :=
  if i.val == 0 then firedNative
  else if i.val == 1 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := true }

/-- Root at 0, one clean dummy at 1, signals 1 on 2..7.
    There is a co-located OLD request/grant at 2 and a separate
    warm grant at 4, which remains present throughout the birth. -/
private def grantDrainWitnessBefore : GrantDrainState 8 Unit :=
  { native := grantDrainWitnessNative
    request := fun i => i.val == 2
    grant := fun i => i.val == 2 || i.val == 4
    scratch := ()
    history := [] }

private def grantDrainWitnessAfter : GrantDrainState 8 Unit :=
  grantDrainStep grantDrainWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWitnessBefore (2 : Fin 8)

private theorem grantDrainWitness_PPlus :
    PPlus grantDrainWitnessRing grantDrainWitnessBefore.native := by
  decide

private theorem grantDrainWitness_clean :
    C_native grantDrainWitnessRing grantDrainWitnessBefore.native := by
  decide

private theorem grantDrainWitness_fire :
    grantDrainSelect grantDrainWitnessRing grantDrainWitnessBefore
      (2 : Fin 8) = .leftLocal := by
  decide

private theorem grantDrainWitness_birth :
    (grantDrainWitnessAfter.native (2 : Fin 8)).l = true := by
  decide

private theorem grantDrainWitness_spends :
    grantDrainWitnessAfter.grant (2 : Fin 8) = false := by
  decide

private theorem grantDrainWitness_survives :
    grantDrainWitnessAfter.grant (4 : Fin 8) = true := by
  decide

private theorem grantDrainWitness_warm_before :
    grantDrainWarmRank grantDrainWitnessRing
      grantDrainWitnessBefore.native (4 : Fin 8) = 3 := by
  decide

private theorem grantDrainWitness_warm_after :
    grantDrainWarmRank grantDrainWitnessRing
      grantDrainWitnessAfter.native (4 : Fin 8) = 4 := by
  decide

/-- A real F0 birth consumes a DIFFERENT old grant and raises
    the surviving label's actual warm rank from 3 to 4.
    The paper explicitly allows +1 here and charges it to a birth.
    Therefore a claimed every-edge nonincrease of the raw D.6 rank
    is not a valid premise for a direct nominated-edge theorem. -/
theorem grantDrainWarmRank_not_globally_nonincreasing :
    ¬ grantDrainWarmRank grantDrainWitnessRing
        grantDrainWitnessAfter.native (4 : Fin 8) ≤
      grantDrainWarmRank grantDrainWitnessRing
        grantDrainWitnessBefore.native (4 : Fin 8) := by
  rw [grantDrainWitness_warm_before, grantDrainWitness_warm_after]
  decide

theorem grantDrainWitness_birth_charge :
    grantDrainWarmRank grantDrainWitnessRing
      grantDrainWitnessAfter.native (4 : Fin 8) ≤
    grantDrainWarmRank grantDrainWitnessRing
      grantDrainWitnessBefore.native (4 : Fin 8) + 1 := by
  rw [grantDrainWitness_warm_before, grantDrainWitness_warm_after]
  decide

/-! ## Finite-horizon theorem interface and ceiling -/

/-- Exact integral ceiling of the paper's 109*n²/3 comparison bound.
    This is not yet proved as a uniform cost of the reference. -/
def grantDrainCeiling (n : Nat) : Nat :=
  (109 * (n * n) + 2) / 3

theorem grantDrainCeiling_le_forty (n : Nat) :
    grantDrainCeiling n ≤ 40 * n * n := by
  unfold grantDrainCeiling
  rw [Nat.mul_assoc 40 n n]
  generalize n * n = X
  omega

/-- The exact costNumerator interface for ANY adapted
    hostile request rule.  This is conditional on a VERIFIED rank,
    including its bound at the actual starting state.  D.6 alone
    cannot discharge hnoninc, as the witness above demonstrates.

    Unlike a paper claim, all unproved hypotheses are explicit. -/
theorem grantDrain_cost_of_certified_nominated_rank
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (rank : GrantDrainState n Scratch → Nat)
    (chosen : GrantDrainState n Scratch → Fin n)
    (hdrop : ∀ s, ¬ GrantFree s →
      rank (grantDrainStep ring freshRequest updateScratch s (chosen s)) + 1 ≤
        rank s)
    (hnoninc : ∀ s, ¬ GrantFree s → ∀ e,
      rank (grantDrainStep ring freshRequest updateScratch s e) ≤ rank s)
    (s : GrantDrainState n Scratch)
    (hbudget : n * rank s ≤ grantDrainCeiling n) :
    ∀ T,
      costNumerator (grantDrainStep ring freshRequest updateScratch)
        (fun z : GrantDrainState n Scratch => GrantFree z) s T ≤
        n ^ T * grantDrainCeiling n := by
  intro T
  calc
    costNumerator (grantDrainStep ring freshRequest updateScratch)
      (fun z : GrantDrainState n Scratch => GrantFree z) s T ≤
        n ^ T * (n * rank s) :=
      Prob.costNumerator_le_of_nominated_edge
        (grantDrainStep ring freshRequest updateScratch)
        (fun z : GrantDrainState n Scratch => GrantFree z)
        rank chosen hdrop hnoninc s T
    _ ≤ n ^ T * grantDrainCeiling n :=
      Nat.mul_le_mul_left _ hbudget

/-- Also a verified (but terminal-only) unconditional cost fact. -/
theorem grantDrain_cost_zero_at_empty
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (h : GrantFree s) (T : Nat) :
    costNumerator (grantDrainStep ring freshRequest updateScratch)
      (fun z : GrantDrainState n Scratch => GrantFree z) s T = 0 := by
  exact costNumerator_terminal
    (grantDrainStep ring freshRequest updateScratch)
    (fun z : GrantDrainState n Scratch => GrantFree z) s h T

end L3


/-!
Repair.  The fire selector and Protocol assembler
are checked separately; full tokenStep-to-reference fidelity is still an
explicit unproved obligation.  Charged warm ghost quota and n=8 control
are included as kernel-checkable statements.
-/

namespace L3

/-! ## (1) Literal two-site faithfulness checks -/

/-- Canonical F0/F1/F2 fire metadata.  Its consumption flags, not merely
    its selected site, are part of the comparison with Base.tokenStep. -/
private def grantDrainBaseFire : GrantDrainFire → Option FireSel
  | .none => none
  | .leftLocal =>
      some { kind := .F0, site := .siteX,
             reqX := true, grantX := true }
  | .rightLocal =>
      some { kind := .F1, site := .siteY,
             reqY := true, grantY := true }
  | .cross =>
      some { kind := .F2, site := .siteX,
             reqX := true, grantY := true }

/-- Pair-local OLD-token/post-E selector. -/
private def grantDrainPairFire {c : Compiled}
    (x y : Agent c) (eX eY : CertNative) : GrantDrainFire :=
  let eligX := !eX.l && eX.b.val == 0
  let eligY := !eY.l && eY.b.val == 0
  if x.req && x.grant && eligX then .leftLocal
  else if y.req && y.grant && eligY then .rightLocal
  else if x.req && y.grant && eligX then .cross
  else .none

/-- The reference priority and old-flag consumption exactly express
    Base.fireSelect, without assuming anything about the other fields. -/
private theorem grantDrainPairFire_base_eq {c : Compiled}
    (x y : Agent c) (eX eY : CertNative) :
    grantDrainBaseFire (grantDrainPairFire x y eX eY) =
      fireSelect x y eX eY := by
  unfold grantDrainPairFire fireSelect
  dsimp only
  by_cases hx :
      (x.req && x.grant && (!eX.l && eX.b.val == 0)) = true
  · simp only [if_pos hx, grantDrainBaseFire]
  · simp only [if_neg hx]
    by_cases hy :
        (y.req && y.grant && (!eY.l && eY.b.val == 0)) = true
    · simp only [if_pos hy, grantDrainBaseFire]
    · simp only [if_neg hy]
      by_cases hc :
          (x.req && y.grant && (!eX.l && eX.b.val == 0)) = true
      · simp only [if_pos hc, grantDrainBaseFire]
      · simp only [if_neg hc, grantDrainBaseFire]

/-- The base BANK/SMALL success bit, before the token owner's T2 guard.
    A success MAY be suppressed, so requiring this bit false would be
    strictly stronger than the lemma's "no new grant produced". -/
private def grantDrainBankWinner (c : Compiled)
    (x y : Agent c) : Bool :=
  if c.useSmall then (smallPair x y c.K).2.2
  else
    bankSuccess (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b

/-!
The token-owner payload comparison is NOT asserted here.  The failed
case-expansion had a heartbeat timeout; a fieldwise lemma relating
Base.tokenStep and grantDrainTokenRow under the *actual* prodGrantX=false
premise remains to be proved.  A Boolean selector theorem
above does not by itself give token-step fidelity.
-/

/-- The Protocol assembler retains native and token fields of its
    base-agent argument.  This is independent of the BANK or DCC client. -/
private theorem grantDrain_assemble_token_frame {c : Compiled}
    (base cert hk : Agent c) :
    (assemble base cert hk).certNative = base.certNative ∧
    (assemble base cert hk).req = base.req ∧
    (assemble base cert hk).grant = base.grant := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Protocol transition's request/grant fields are the base
    projection; the missing fieldwise tokenStep theorem must still
    connect baseStep to grantDrainTokenRow. -/
private theorem grantDrain_transition_base_token_frame (c : Compiled)
    (x y : Agent c) :
    let ev := (certificateStep c x y).2.2
    (transition c x y).1.req = (baseStep c ev x y).1.req ∧
    (transition c x y).1.grant = (baseStep c ev x y).1.grant ∧
    (transition c x y).2.req = (baseStep c ev x y).2.req ∧
    (transition c x y).2.grant = (baseStep c ev x y).2.grant := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A projection carrying enough private scratch to reconstruct the
    actual DCC decision; the caller supplies its explicit edge history. -/
def grantDrainRealProjection {n q : Nat}
    (C : (protocol q).Configuration n) (history : List (Fin n)) :
    GrantDrainState n ((protocol q).Configuration n) :=
  { native := nativeProjection C
    request := fun i => (C i).req
    grant := fun i => (C i).grant
    scratch := C
    history := history }

/-- The actual OLD-certificate/DCC request bit, read after revealing e.
    Hostile reference policies may choose a different bit; faithfulness
    to the physical protocol fixes the policy to THIS one. -/
def grantDrainRealFresh {n q : Nat}
    (ring : DirectedRing n)
    (s : GrantDrainState n ((protocol q).Configuration n))
    (e : Fin n) : Bool :=
  let x := s.scratch e
  let y := s.scratch (ring.rightNeighbor e)
  (dccStep x y (certificateStep (compileAdvice q) x y).2.2).request

/-- The corresponding full scratch update. -/
def grantDrainRealScratchNext {n q : Nat}
    (ring : DirectedRing n)
    (s : GrantDrainState n ((protocol q).Configuration n))
    (e : Fin n) : (protocol q).Configuration n :=
  (protocol q).step ring s.scratch e

/-- The *exact* per-service comparison hypothesis.  It does NOT say
    that the BANK lottery failed; it says the token owner actually
    emitted no new grant after FIRE and leader sinks. -/
def grantDrainNoRealGrantProduced {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n) : Prop :=
  let x := C e
  let y := C (ring.rightNeighbor e)
  let post := certLiteralEPair x.certNative y.certNative
  let fire := fireSelect x y post.1 post.2
  let fX := if fireAtSite fire .siteX then firedNative else post.1
  let fY := if fireAtSite fire .siteY then firedNative else post.2
  let fresh := (dccStep x y
    (certificateStep (compileAdvice q) x y).2.2).request
  (tokenStep x y fX fY fire fresh
    (grantDrainBankWinner (compileAdvice q) x y)).2.2.prodGrantX = false

/-! ## (2) Proof-only ancestry and charged D.7 warm quota -/

/-- The paper's one tracked initial physical grant.  This is a proof
    ghost, not a protocol field.  When grants coalesce, separate ghosts
    may have the SAME host: the two labels form a union, not a copy.
    The remaining-birth allowance is global work prepaid to EACH
    tracked label (at most n births total), not a duplicated grant. -/
structure GrantDrainWarmLabel (n : Nat) where
  identity : Fin n
  host : Option (Fin n)
  warm : Bool
  birthsLeft : Nat
  exceptionalLeft : Bool

/-- This stage predicate is intentionally only the syntactic warm
    guard; D.7 also needs an actual C_native sector hypothesis. -/
def grantDrainWarmAt {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) (g : Fin n) : Bool :=
  !(s.native g).l && ((s.native g).b.val == 0) &&
    (s.native g).sg && !(s.request g)

/-- Native leader-death test for the paper's single exceptional
    unshielded, signal-zero, bullet-free-source situation.
    It is evaluated on the OLD tracked sector; a canonical birth
    never masquerades as a native death. -/
def grantDrainExceptionalDeath {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (g : Fin n) : Bool :=
  let d := grantDrainLeftLeaderDistance ring s.native g
  let p := PPL.shiftLeft ring g d
  (s.native p).l &&
    !(s.native p).sh &&
    !(s.native p).sg &&
    (grantDrainLeftBulletDistance ring s.native g d).isNone &&
    !(nativeE ring s.native e p).l

/-- Transport one initial grant identity through the literal
    no-new-grant token row.  On a Y->X move, the old Y label joins
    whatever label was already at X.  F0/F1/F2 or sinks retire the
    consumed identity.  An untouched site's label stays there.

    The ancestry is not read from stored protocol state: a separate
    preservation/simulation theorem is still required. -/
def grantDrainWarmLabelStep {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) : GrantDrainWarmLabel n :=
  let y := ring.rightNeighbor e
  let fire := grantDrainSelect ring s e
  let N' := grantDrainNativeNext ring s e
  let row := grantDrainTokenRow (s.request e) (s.grant e)
    (s.request y) (s.grant y) (N' e).l (N' y).l
    (freshRequest s e) fire
  let host' :=
    match label.host with
    | none => none
    | some g =>
        if g = e then
          if row.1.grant then some e else none
        else if g = y then
          if fire = .rightLocal ∨ fire = .cross ∨
             (N' e).l = true ∨ (N' y).l = true then none
          else if s.request y && s.grant y then some y
          else if row.1.grant then some e else none
        else some g
  let step' := grantDrainStep ring freshRequest updateScratch s e
  let warm' :=
    match host' with
    | none => false
    | some g => label.warm && grantDrainWarmAt step' g
  let exceptionalUsed :=
    match label.host with
    | none => false
    | some g => label.warm && grantDrainExceptionalDeath ring s e g
  { label with
    host := host'
    warm := warm'
    birthsLeft :=
      if fire = .none then label.birthsLeft else label.birthsLeft - 1
    exceptionalLeft := label.exceptionalLeft && !exceptionalUsed }

/-- Each tracked label's birth and exceptional allowances only shrink.
    This is a pure ghost-accounting invariant, not the difficult
    machine-specific warm-rank inequality. -/
theorem grantDrainWarmLabel_birthsLeft_le {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (freshRequest : GrantDrainState n Scratch → Fin n → Bool)
    (updateScratch : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (label : GrantDrainWarmLabel n) :
    (grantDrainWarmLabelStep ring freshRequest updateScratch s e
      label).birthsLeft ≤ label.birthsLeft := by
  change (if grantDrainSelect ring s e = GrantDrainFire.none
    then label.birthsLeft else label.birthsLeft - 1) ≤
      label.birthsLeft
  by_cases h : grantDrainSelect ring s e = GrantDrainFire.none
  · simpa only [if_pos h] using (Nat.le_refl label.birthsLeft)
  · simpa only [if_neg h] using (Nat.sub_le label.birthsLeft 1)

/-- W plus the prepaid birth allowance plus the one-time exceptional
    native-death reserve, while the tracked identity remains warm.
    On retirement or marking cold, this stage-specific quota is zero.
    It is not an all-stages drift function. -/
def grantDrainChargedWarmRank {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (label : GrantDrainWarmLabel n) : Nat :=
  if label.warm then
    match label.host with
    | none => 0
    | some g =>
        if s.grant g then
          grantDrainWarmRank ring s.native g + label.birthsLeft +
            (if label.exceptionalLeft then 2 * (n - 2) else 0)
        else 0
  else 0

/-- The exact algebra that a charged D.6 transition needs:
    each increase in W must be paid from spent birth or exceptional
    credit.  The two missing premises are deliberately explicit. -/
theorem grantDrainWarmQuota_nonincrease_of_paid_increment
    (w w' b b' d d' : Nat)
    (hb : b' ≤ b) (hd : d' ≤ d)
    (hw : w' ≤ w + (b - b') + (d - d')) :
    w' + b' + d' ≤ w + b + d := by
  omega

/-- The nominated-edge version requires one EXTRA unit of progress,
    beyond any allowance consumed by simultaneous births/deaths. -/
theorem grantDrainWarmQuota_strict_of_paid_increment
    (w w' b b' d d' : Nat)
    (hb : b' ≤ b) (hd : d' ≤ d)
    (hw : w' + 1 ≤ w + (b - b') + (d - d')) :
    w' + b' + d' + 1 ≤ w + b + d := by
  omega

/-! ## Required n=8 regression: the offending uncharged birth is
    exactly paid for by one unit of the surviving grant's allowance. -/

private def grantDrainWitnessWarmLabel : GrantDrainWarmLabel 8 :=
  { identity := (4 : Fin 8)
    host := some (4 : Fin 8)
    warm := true
    birthsLeft := 2
    exceptionalLeft := true }

private def grantDrainWitnessWarmLabelAfter : GrantDrainWarmLabel 8 :=
  grantDrainWarmLabelStep grantDrainWitnessRing
    (fun _ _ => false) (fun _ _ => ())
    grantDrainWitnessBefore (2 : Fin 8)
    grantDrainWitnessWarmLabel

/-- The BEFORE value is W=3, two remaining grant-funded births,
    and 2*(8-2)=12 of exceptional-death reserve. -/
theorem grantDrainWitnessChargedWarm_before :
    grantDrainChargedWarmRank grantDrainWitnessRing
      grantDrainWitnessBefore grantDrainWitnessWarmLabel = 17 := by
  decide

/-- F0 spends the site-2 grant; the site-4 label survives, remains
    warm, and has W=4 with only one birth allowance remaining. -/
theorem grantDrainWitnessChargedWarm_after :
    grantDrainChargedWarmRank grantDrainWitnessRing
      grantDrainWitnessAfter grantDrainWitnessWarmLabelAfter = 17 := by
  decide

/-- Kernel-checkable charged form of the earlier n=8 counterexample.
    Equality (rather than strict drop) is expected: e_2 is a
    REMOTE birth, not the warm label's nominated incoming edge. -/
theorem grantDrainWitnessChargedWarm_nonincrease :
    grantDrainChargedWarmRank grantDrainWitnessRing
      grantDrainWitnessAfter grantDrainWitnessWarmLabelAfter ≤
    grantDrainChargedWarmRank grantDrainWitnessRing
      grantDrainWitnessBefore grantDrainWitnessWarmLabel := by
  rw [grantDrainWitnessChargedWarm_before,
    grantDrainWitnessChargedWarm_after]
  decide

end L3
