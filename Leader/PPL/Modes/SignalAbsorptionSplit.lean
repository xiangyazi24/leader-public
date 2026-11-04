import Leader.PPL.Modes.SignalAbsorption

namespace PPL.Modes.Lemma9

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage

/-- The arm-0 tag assigned by initialGhost to the signal initially at i. -/
def lemma9Tag {n : Nat} (i : Fin n) : SignalTag n :=
  { origin := i, arm := 0 }

/--
Prefix-measurable stop for the tagged signal.
Stopping means that the original arm-0 lineage is no longer physically alive;
absorption, TTL disappearance, and line-35 re-arm all count as success.
-/
def lemma9Stop
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre : List (Fin n)) : Bool :=
  !tagAliveB
    (ghostRun ring (initialGhost C) pre)
    (lemma9Tag i)

/--
Deterministic paper-Lemma-9 coupling.

While the arm-0 tag is alive, host chooses its unique current physical site
from the already-consumed scheduler prefix.  On a full-horizon word where the
tag is still alive, either fewer than E stopped encounters occurred, or the
first E H/T encounter marks contain at most kappa = lotteryTarget psi c wins.

This is the genuinely new run fact.  Its one-step proof is to be built from
the literal DetermineMode row together with SignalLineageOwnership:
max-TTL ownership, no cloning, re-arm termination, tag-TTL nonincrease, and
moved-winner hits reset.
-/
def Lemma9LineageFailureSplit : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hkappa : kappa = 8 * c * psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (i : Fin n),
    0 < (C i).signalR.val →
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring →
    ∃ host : List (Fin n) → Fin n,
      (∀ pre : List (Fin n),
        lemma9Stop ring C i pre = false →
        (ghostRun ring (initialGhost C) pre).owner (host pre) =
          some (lemma9Tag i)) ∧
      lemma9FailureCount ring C i c ≤
        stoppedPredictableHostLowerFailureCount
            ring host (lemma9Stop ring C i)
            (lemma9T n psi c) (lemma9E psi c) +
          stoppedLotteryLowerFailureCount
            psi (C i).hits.val
            ring host (lemma9Stop ring C i)
            (lemma9T n psi c) (lemma9E psi c)
            (lotteryTarget psi c)

/--
Finite-word encounter lower tail used by paper Lemma 9.

PredictableHostTails supplies the exact two-hot-letter projection.  The
remaining work is the Nat specialization at T = n*E showing that the
strict lower tail costs at most 3/n^2 of scheduler space.
-/
def Lemma9EncounterLowerTail : Prop :=
  ∀ {n psi c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 6 ≤ c)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (host : List (Fin n) → Fin n)
      (stop : List (Fin n) → Bool),
    PredictableHostTails →
    n * n *
        stoppedPredictableHostLowerFailureCount
          ring host stop
          (lemma9T n psi c) (lemma9E psi c) ≤
      3 * n ^ lemma9T n psi c

/--
Finite-word stopped lottery lower tail used by paper Lemma 9.

The intended discharge is exactly:
ModeStoppedTreeTransfer.lower,
then WLGHeadOffsetBounds for arbitrary initial hits,
then LotteryCountBounds/Lemma 8,
and finally n^2 ≤ 2^(c*psi).
-/
def Lemma9LotteryLowerTail : Prop :=
  ∀ {n psi c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 6 ≤ c)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (host : List (Fin n) → Fin n)
      (stop : List (Fin n) → Bool)
      (h : Nat),
    h ≤ psi →
    ModeStoppedTreeTransfer →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    n * n *
        stoppedLotteryLowerFailureCount
          psi h ring host stop
          (lemma9T n psi c) (lemma9E psi c)
          (lotteryTarget psi c) ≤
      n ^ lemma9T n psi c

/--
Assembly of paper Lemma 9 from the three proof steps above.

There is no protocol reasoning here.  The deterministic split gives two bad
numerators, the two counting Props bound them, and the final 3+1 union is the
constant 4 already frozen in Lemma9WordBound.
-/
theorem lemma9Bridge_of_split
    (hphysical : Lemma9LineageFailureSplit)
    (hencounter : Lemma9EncounterLowerTail)
    (hlottery : Lemma9LotteryLowerTail) :
    Lemma9DeterministicBridge := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring C i hsignal hlineage
  intro hmarked hpredict hhead hcount
  rcases
      hphysical hn3 hpsi hkappa
        ring C i hsignal hlineage with
    ⟨host, hhost, hsplit⟩
  have hhits : (C i).hits.val ≤ psi := by
    have hlt := (C i).hits.isLt
    omega
  have henc :
      n * n *
          stoppedPredictableHostLowerFailureCount
            ring host (lemma9Stop ring C i)
            (lemma9T n psi c) (lemma9E psi c) ≤
        3 * n ^ lemma9T n psi c :=
    hencounter hn3 hpsi hc hnpow
      ring host (lemma9Stop ring C i) hpredict
  have hlot :
      n * n *
          stoppedLotteryLowerFailureCount
            psi (C i).hits.val
            ring host (lemma9Stop ring C i)
            (lemma9T n psi c) (lemma9E psi c)
            (lotteryTarget psi c) ≤
        n ^ lemma9T n psi c :=
    hlottery hn3 hpsi hc hnpow
      ring host (lemma9Stop ring C i)
      (C i).hits.val hhits
      hmarked hhead hcount
  unfold Lemma9WordBound
  calc
    n * n * lemma9FailureCount ring C i c ≤
        n * n *
          (stoppedPredictableHostLowerFailureCount
              ring host (lemma9Stop ring C i)
              (lemma9T n psi c) (lemma9E psi c) +
            stoppedLotteryLowerFailureCount
              psi (C i).hits.val
              ring host (lemma9Stop ring C i)
              (lemma9T n psi c) (lemma9E psi c)
              (lotteryTarget psi c)) :=
      Nat.mul_le_mul_left (n * n) hsplit
    _ =
        n * n *
            stoppedPredictableHostLowerFailureCount
              ring host (lemma9Stop ring C i)
              (lemma9T n psi c) (lemma9E psi c) +
          n * n *
            stoppedLotteryLowerFailureCount
              psi (C i).hits.val
              ring host (lemma9Stop ring C i)
              (lemma9T n psi c) (lemma9E psi c)
              (lotteryTarget psi c) := by
      rw [Nat.mul_add]
    _ ≤
        3 * n ^ lemma9T n psi c +
          n ^ lemma9T n psi c :=
      Nat.add_le_add henc hlot
    _ = 4 * n ^ lemma9T n psi c := by
      omega

end PPL.Modes.Lemma9

#print axioms PPL.Modes.Lemma9.lemma9Bridge_of_split
