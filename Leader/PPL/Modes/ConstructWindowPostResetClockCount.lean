import Leader.PPL.Modes.ConstructionModeSplit
import Leader.PPL.Probability.MarkedWordTransfer
import Leader.PPL.Probability.LotteryMoment
import Leader.Core.FiniteUniformStoppingTree

/-!
# P_PL Lemma 5(ii): post-reset clock count

Truth verdict: the frozen leaf is TRUE.

The binary counting layer closes with the existing padded marked-word transfer,
the arbitrary-head-offset coupling, and the proved Lemma-7 moment bound.  The
one remaining physical statement is isolated below as
`Lemma5iiPostResetClockProjection`.

That residual is wordwise, not probabilistic: on a word with the fixed-agent
encounter cap and a failure of `constructAlong`, select the first agent that
enters Detect and the latest reset epoch for that agent.  The clock started at
at most kappa/2; a later reset restarts it at zero, so reaching Detect forces
at least kappa/2 physical clock ticks in the selected epoch.
`clockSuffixTickLotteryBridge` turns those ticks into lottery wins.  Passing
from the selected epoch's actual head offset to the full fixed-agent H/T word
costs at most the one-win offset slack; the frozen use of `c - 1` has much
more than that slack.  The encounter-good premise supplies the padded
`lemma5iiEncounterCap` bound.

No new concentration inequality is hidden in the residual.
-/

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-- Fixed-agent padded upper event used after the physical reset projection. -/
def lemma5iiPostResetAgentBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat)
    (x : Fin n)
    (word : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits ring
      (fun _ => x) (fun _ => false) word
  decide
    (And
      (bits.length <= lemma5iiEncounterCap psi c)
      (lotteryTarget psi (c - 1) + 1 <=
        (lotteryRun psi
          (lotteryOffset (C x).hits.val) bits).wins))

def lemma5iiPostResetAgentFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat)
    (x : Fin n) : Nat :=
  (allSchedules n
    (lemma5iiHorizon n psi kappa)).countP
      (lemma5iiPostResetAgentBadB ring C c x)

/--
The single remaining physical leaf.

This is strictly wordwise.  It contains no scheduler count and no tail bound.
The intended proof chooses the first Detect witness, then its latest physical
clock reset.  If there was no reset, the empty prefix is the epoch start.
The corrected stopped-clock machinery and `clockSuffixTickLotteryBridge`
supply the reset/tick semantics; the rest is fixed-agent H/T bookkeeping.
-/
def Lemma5iiPostResetClockProjection : Prop :=
  forall {n psi kappa c : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hc : 3 <= c)
      (hkappa : kappa = 16 * c * psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    midPhysicalB C = true ->
    lemma5iiPostResetClockBadB ring C c word = true ->
      exists x : Fin n,
        lemma5iiPostResetAgentBadB ring C c x word = true

private def postResetAnyPred {A : Type} :
    List (A -> Bool) -> A -> Bool
  | [], _ => false
  | p :: ps, x => p x || postResetAnyPred ps x

private def postResetAnyPred_true_of_mem
    {A : Type}
    (ps : List (A -> Bool))
    (p : A -> Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    postResetAnyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [postResetAnyPred, hp]
      · have ht := ih hq
        simp [postResetAnyPred, ht]

private def postResetCountP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

private def postResetCountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private def postResetCountP_anyPred_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A -> Bool)) :
    xs.countP (postResetAnyPred ps) <=
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [postResetAnyPred]
  | cons p ps ih =>
      calc
        xs.countP (postResetAnyPred (p :: ps)) =
            xs.countP
              (fun x => p x || postResetAnyPred ps x) := by
          rfl
        _ <= xs.countP p +
            xs.countP (postResetAnyPred ps) :=
          postResetCountP_or_le_add
            xs p (postResetAnyPred ps)
        _ <= xs.countP p +
            (ps.map (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
            ((p :: ps).map
              (fun q => xs.countP q)).sum := by
          simp

/--
One fixed agent costs at most the Lemma-7 upper tail with parameter c-1.

The +1 threshold is exactly the arbitrary-head-offset loss:
offset wins >= M+1 implies fresh wins >= M.
-/
theorem lemma5iiPostResetAgentCount
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 3 <= c)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x : Fin n)
    (hoffset : WLGHeadOffsetBounds)
    (hcount : LotteryCountBounds) :
    2 ^ ((c - 1) * psi) *
        lemma5iiPostResetAgentFailureCount
          ring C c x <=
      n ^ lemma5iiHorizon n psi kappa := by
  let T : Nat := lemma5iiHorizon n psi kappa
  let E : Nat := lemma5iiEncounterCap psi c
  let M : Nat := lotteryTarget psi (c - 1)
  let h : Nat := (C x).hits.val
  let A : Nat :=
    lemma5iiPostResetAgentFailureCount ring C c x
  let B : Nat :=
    lotteryAtLeastWordCount psi h E (M + 1)
  let B0 : Nat :=
    lotteryAtLeastWordCount psi 0 E M
  let scale : Nat := 2 ^ ((c - 1) * psi)

  change scale * A <= n ^ T

  have hh : h <= psi := by
    dsimp [h]
    have hlt := (C x).hits.isLt
    omega

  have htransfer0 :=
    stoppedEncounterLotteryAtLeast_padded_transfer
      hn3 psi h ring
      (fun _ => x)
      (fun _ => false)
      T E (M + 1)

  have htransfer :
      A * 2 ^ E <= n ^ T * B := by
    dsimp [A, B]
    unfold lemma5iiPostResetAgentFailureCount
    delta lemma5iiPostResetAgentBadB
    simpa [lemma5iiPostResetAgentFailureCount,
      lemma5iiPostResetAgentBadB,
      stoppedMarkedPaddedCount,
      E, M, T, decide_eq_true_eq] using htransfer0

  have hhead : B <= B0 := by
    dsimp [B, B0]
    exact
      (hoffset psi h E M
        (by omega) hh).2.1

  have hL7 :
      scale * B0 <= 2 ^ E := by
    dsimp [scale, B0, E, M]
    unfold lemma5iiEncounterCap
    exact
      (hcount psi (c - 1)
        (by omega) (by omega)).1

  have hscaled :
      (scale * A) * 2 ^ E <=
        n ^ T * 2 ^ E := by
    calc
      (scale * A) * 2 ^ E =
          scale * (A * 2 ^ E) := by
        ac_rfl
      _ <= scale * (n ^ T * B) :=
        Nat.mul_le_mul_left scale htransfer
      _ = n ^ T * (scale * B) := by
        ac_rfl
      _ <= n ^ T * (scale * B0) :=
        Nat.mul_le_mul_left (n ^ T)
          (Nat.mul_le_mul_left scale hhead)
      _ <= n ^ T * 2 ^ E :=
        Nat.mul_le_mul_left (n ^ T) hL7

  exact
    Nat.le_of_mul_le_mul_right
      hscaled
      (Nat.pow_pos (by omega : 0 < 2))

/--
The requested counting leaf, conditional only on the single physical
projection above.

All stochastic/counting inputs of the frozen statement are retained verbatim.
The corrected stopped-clock and stopped-tree premises are not replaced; the
bounded-round residual isolates the deterministic consequence that still has
to be wired from those physical interfaces.
-/
theorem lemma5iiPostResetClockCount
    (hprojection : Lemma5iiPostResetClockProjection) :
    Lemma5iiPostResetClockCount := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring C
  intro hmid
  intro _hlineage
  intro _hclock
  intro _hmarked
  intro hoffset
  intro hcount

  let T : Nat := lemma5iiHorizon n psi kappa
  let scale : Nat := 2 ^ ((c - 1) * psi)
  let words : List (DetSchedule n) := allSchedules n T
  let bad : DetSchedule n -> Bool :=
    lemma5iiPostResetClockBadB ring C c
  let agentPred : Fin n -> DetSchedule n -> Bool :=
    fun x => lemma5iiPostResetAgentBadB ring C c x
  let agentCount : Fin n -> Nat :=
    fun x => words.countP (agentPred x)
  let preds : List (DetSchedule n -> Bool) :=
    List.ofFn agentPred
  let F : Nat :=
    lemma5iiPostResetClockFailureCount ring C c

  have hbadToAny :
      forall word,
        bad word = true ->
          postResetAnyPred preds word = true := by
    intro word hbad
    obtain ⟨x, hx⟩ :=
      hprojection
        hn3 hpsi hc hkappa
        ring C word hmid hbad
    apply
      postResetAnyPred_true_of_mem
        preds (agentPred x) word
    · dsimp [preds]
      rw [List.mem_ofFn]
      exact ⟨x, rfl⟩
    · exact hx

  have hunion :
      F <= (List.ofFn agentCount).sum := by
    calc
      F = words.countP bad := by
        rfl
      _ <=
          words.countP (postResetAnyPred preds) :=
        postResetCountP_mono
          words bad (postResetAnyPred preds)
          hbadToAny
      _ <=
          (preds.map
            (fun p => words.countP p)).sum :=
        postResetCountP_anyPred_le_sum
          words preds
      _ = (List.ofFn agentCount).sum := by
        dsimp [preds, agentCount, agentPred]
        rw [List.map_ofFn]
        rfl

  have hagent :
      forall x : Fin n,
        scale * agentCount x <= n ^ T := by
    intro x
    dsimp [scale, agentCount, agentPred, words, T]
    exact
      lemma5iiPostResetAgentCount
        hn3 hpsi hc ring C x
        hoffset hcount

  have hsum :
      (List.ofFn
        (fun x : Fin n =>
          scale * agentCount x)).sum <=
        (List.ofFn
          (fun _ : Fin n => n ^ T)).sum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun x : Fin n =>
        scale * agentCount x)
      (fun _ : Fin n => n ^ T)
      hagent

  have hsum' :
      scale * (List.ofFn agentCount).sum <=
        n * n ^ T := by
    calc
      scale * (List.ofFn agentCount).sum =
          (List.ofFn
            (fun x : Fin n =>
              scale * agentCount x)).sum :=
        (FiniteUniformStoppingTree.ofFn_sum_mul_left
          scale agentCount).symm
      _ <=
          (List.ofFn
            (fun _ : Fin n => n ^ T)).sum :=
        hsum
      _ = n * n ^ T :=
        FiniteUniformStoppingTree.ofFn_sum_const
          n (n ^ T)

  have hscaledF :
      scale * F <= n * n ^ T :=
    Nat.le_trans
      (Nat.mul_le_mul_left scale hunion)
      hsum'

  have hsq :
      n * n <= 2 ^ psi * 2 ^ psi :=
    Nat.mul_le_mul hnpow hnpow

  have hpowSquare :
      2 ^ psi * 2 ^ psi =
        2 ^ (2 * psi) := by
    rw [← Nat.pow_add]
    congr 1
    omega

  have htwo :
      2 <= c - 1 := by
    omega

  have hexp :
      2 * psi <= (c - 1) * psi := by
    exact Nat.mul_le_mul_right psi htwo

  have hpowMono :
      2 ^ (2 * psi) <=
        2 ^ ((c - 1) * psi) :=
    Nat.pow_le_pow_right
      (by omega : 0 < 2) hexp

  have hcoef :
      n * n <= scale := by
    dsimp [scale]
    calc
      n * n <= 2 ^ psi * 2 ^ psi := hsq
      _ = 2 ^ (2 * psi) := hpowSquare
      _ <= 2 ^ ((c - 1) * psi) := hpowMono

  have hnnF :
      (n * n) * F <= n * n ^ T :=
    Nat.le_trans
      (Nat.mul_le_mul_right F hcoef)
      hscaledF

  have hnpos : 0 < n := by
    omega

  have hcancellable :
      n * (n * F) <= n * n ^ T := by
    simpa [Nat.mul_assoc] using hnnF

  have hstrong :
      n * F <= n ^ T :=
    Nat.le_of_mul_le_mul_left
      hcancellable hnpos

  have hstrong' :
      n *
          lemma5iiPostResetClockFailureCount
            ring C c <=
        n ^ lemma5iiHorizon n psi kappa := by
    simpa [F, T] using hstrong

  exact Nat.le_trans hstrong' (by omega)

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iiPostResetAgentCount
#print axioms PPL.Modes.Lemma5.lemma5iiPostResetClockCount
