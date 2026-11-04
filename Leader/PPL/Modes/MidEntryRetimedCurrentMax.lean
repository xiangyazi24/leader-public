import Leader.PPL.Modes.MidEntryResetModeCap
import Leader.PPL.Modes.ConstructWindowPostResetStep
import Leader.PPL.Modes.MidEntryRetimedCounts

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
# Lemma 5(i): current-max retimed splice

The fixed-arm suffix interfaces are not stable under moving the boundary to
the first configuration carrying a max reset.  These two state-rooted
interfaces are the endpoint-retaining versions needed by the first-terminal
bind.
-/

def Lemma5iRetimedTraversalCurrentMaxSuffixProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    maxResetSignalB D = true ->
    (allSchedules n (lemma5SweepHorizon n)).countP
        (fun suffix =>
          !allClockResetsSeenB ring D
            (suffix.take (lemma5PaperSweepHorizon n))) <=
      n ^ (2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n)

def Lemma5iRetimedMidCurrentMaxSuffixBound : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    neverLeaderless ring D ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    maxResetSignalB D = true ->
    (allSchedules n (lemma5SweepHorizon n)).countP
        (fun suffix =>
          let sweep :=
            suffix.take (lemma5PaperSweepHorizon n)
          allClockResetsSeenB ring D sweep &&
            !(reachesAux ring midPhysicalB D sweep)) *
        2 ^ psi <=
      n ^ lemma5SweepHorizon n

/-! ## Local public mirrors of the private retimed recursion -/

private def q19708RetimedTraversalBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          (word.take (lemma5PaperSweepHorizon n))
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C []
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          ((e :: rest).take (lemma5PaperSweepHorizon n))
      else
        q19708RetimedTraversalBadAux
          ring (pplStep ring C e) fuel rest

private def q19708RetimedMidClockBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        let sweep :=
          word.take (lemma5PaperSweepHorizon n)
        allClockResetsSeenB ring C sweep &&
          !(reachesAux ring midPhysicalB C sweep)
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        allClockResetsSeenB ring C [] &&
          !(reachesAux ring midPhysicalB C [])
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        let sweep :=
          (e :: rest).take
            (lemma5PaperSweepHorizon n)
        allClockResetsSeenB ring C sweep &&
          !(reachesAux ring midPhysicalB C sweep)
      else
        q19708RetimedMidClockBadAux
          ring (pplStep ring C e) fuel rest

private def q19708TraversalCurrentMaxBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (suffix : DetSchedule n) : Bool :=
  !allClockResetsSeenB ring D
    (suffix.take (lemma5PaperSweepHorizon n))

private def q19708MidCurrentPaperBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (sweep : DetSchedule n) : Bool :=
  allClockResetsSeenB ring D sweep &&
    !(reachesAux ring midPhysicalB D sweep)

private def q19708MidCurrentMaxBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (suffix : DetSchedule n) : Bool :=
  q19708MidCurrentPaperBadB ring D
    (suffix.take (lemma5PaperSweepHorizon n))

/-- Unfold the private retimed recursions of `Lemma5iRetimedSplit.lean`
(same pattern as `unfoldFinishModes` in `ClockSuffixBridge.lean`). -/
elab "unfoldRetimedTraversalAux" : tactic => do
  let c := Lean.mkIdent
    ((((((`_private.Leader.PPL.Modes.MidEntryRetimedSplit).num 0).str "PPL").str
      "Modes").str "Lemma5").str "lemma5iRetimedTraversalBadAux")
  let tac ← `(tactic| unfold $c:ident)
  Lean.Elab.Tactic.evalTactic tac

elab "unfoldRetimedMidAux" : tactic => do
  let c := Lean.mkIdent
    ((((((`_private.Leader.PPL.Modes.MidEntryRetimedSplit).num 0).str "PPL").str
      "Modes").str "Lemma5").str "lemma5iRetimedMidClockBadAux")
  let tac ← `(tactic| unfold $c:ident)
  Lean.Elab.Tactic.evalTactic tac

private def q19708TraversalBadB_fun_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iRetimedTraversalBadB ring C =
      q19708RetimedTraversalBadAux
        ring C (lemma5ArmHorizon n) := by
  funext word
  unfold lemma5iRetimedTraversalBadB
  generalize lemma5ArmHorizon n = fuel
  induction fuel generalizing C word with
  | zero =>
      unfoldRetimedTraversalAux
      unfold q19708RetimedTraversalBadAux
      rfl
  | succ fuel ih =>
      cases word with
      | nil =>
          unfoldRetimedTraversalAux
          unfold q19708RetimedTraversalBadAux
          rfl
      | cons e rest =>
          unfoldRetimedTraversalAux
          unfold q19708RetimedTraversalBadAux
          by_cases h : maxResetSignalB C = true
          · simp only [h, if_true, ite_true]
          · simp only [h, if_false, ite_false, Bool.false_eq_true]
            exact ih _ _

private def q19708MidBadB_fun_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iRetimedMidClockBadB ring C =
      q19708RetimedMidClockBadAux
        ring C (lemma5ArmHorizon n) := by
  funext word
  unfold lemma5iRetimedMidClockBadB
  generalize lemma5ArmHorizon n = fuel
  induction fuel generalizing C word with
  | zero =>
      unfoldRetimedMidAux
      unfold q19708RetimedMidClockBadAux
      rfl
  | succ fuel ih =>
      cases word with
      | nil =>
          unfoldRetimedMidAux
          unfold q19708RetimedMidClockBadAux
          rfl
      | cons e rest =>
          unfoldRetimedMidAux
          unfold q19708RetimedMidClockBadAux
          by_cases h : maxResetSignalB C = true
          · simp only [h, if_true, ite_true]
          · simp only [h, if_false, ite_false, Bool.false_eq_true]
            exact ih _ _

private def q19708TraversalAux_eq_currentMax
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (fuel : Nat)
    (word : DetSchedule n)
    (hm : maxResetSignalB C = true) :
    q19708RetimedTraversalBadAux
        ring C fuel word =
      q19708TraversalCurrentMaxBadB
        ring C word := by
  cases fuel with
  | zero =>
      simp [q19708RetimedTraversalBadAux,
        q19708TraversalCurrentMaxBadB, hm]
  | succ fuel =>
      cases word <;>
        simp [q19708RetimedTraversalBadAux,
          q19708TraversalCurrentMaxBadB, hm]

private def q19708MidAux_eq_currentMax
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (fuel : Nat)
    (word : DetSchedule n)
    (hm : maxResetSignalB C = true) :
    q19708RetimedMidClockBadAux
        ring C fuel word =
      q19708MidCurrentMaxBadB
        ring C word := by
  cases fuel with
  | zero =>
      simp [q19708RetimedMidClockBadAux,
        q19708MidCurrentMaxBadB,
        q19708MidCurrentPaperBadB, hm]
  | succ fuel =>
      cases word <;>
        simp [q19708RetimedMidClockBadAux,
          q19708MidCurrentMaxBadB,
          q19708MidCurrentPaperBadB, hm]

/-! ## Finite scheduler algebra -/

private def q19708AllSchedules_add
    (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap
        (fun pre =>
          (allSchedules n b).map
            (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules,
        List.flatMap_assoc,
        List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]

private def q19708SumMapLe
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons]
      exact
        Nat.add_le_add
          (hfg x (by simp))
          (ih (fun y hy => hfg y (by simp [hy])))

private def q19708SumMapConst
    {A : Type}
    (xs : List A)
    (c : Nat) :
    (xs.map (fun _ => c)).sum =
      xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

private def q19708SumMapMulRight
    {A : Type}
    (xs : List A)
    (f : A -> Nat)
    (c : Nat) :
    (xs.map f).sum * c =
      (xs.map (fun x => f x * c)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_mul]

private def q19708SumIfCount
    {A : Type}
    (xs : List A)
    (p : A -> Bool)
    (c : Nat) :
    (xs.map
      (fun x => if p x then c else 0)).sum =
      xs.countP p * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.countP_cons]
      cases hp : p x <;>
        simp [hp, ih, Nat.succ_mul, Nat.add_comm]

private def q19708CountP_prefixInvariant
    {n H P : Nat}
    (p : DetSchedule n -> Bool)
    (hinv :
      forall sweep : DetSchedule n,
        sweep.length = H ->
        forall pad : DetSchedule n,
          p (sweep ++ pad) = p sweep) :
    (allSchedules n (H + P)).countP p =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q19708AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun sweep =>
          ((allSchedules n P).map
            (fun pad => sweep ++ pad)).countP p)) =
      (allSchedules n H).map
        (fun sweep =>
          if p sweep then n ^ P else 0) := by
    apply List.map_congr_left
    intro sweep hsweep
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length
        n H sweep hsweep
    have hfun :
        (fun pad : DetSchedule n =>
          p (sweep ++ pad)) =
        (fun _ : DetSchedule n =>
          p sweep) := by
      funext pad
      exact hinv sweep hlen pad
    rw [hfun]
    cases hp : p sweep <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact q19708SumIfCount
    (allSchedules n H) p (n ^ P)

private def q19708CountP_take_pad
    {n H P : Nat}
    (p : DetSchedule n -> Bool) :
    (allSchedules n (H + P)).countP
        (fun word => p (word.take H)) =
      (allSchedules n H).countP p *
        n ^ P := by
  rw [q19708AllSchedules_add,
    List.countP_flatMap]
  simp only [Function.comp_def]
  have hmap :
      ((allSchedules n H).map
        (fun pre =>
          ((allSchedules n P).map
            (fun pad => pre ++ pad)).countP
              (fun word => p (word.take H)))) =
      (allSchedules n H).map
        (fun pre =>
          if p pre then n ^ P else 0) := by
    apply List.map_congr_left
    intro pre hpre
    rw [List.countP_map]
    simp only [Function.comp_def]
    have hlen :=
      allSchedules_schedule_length n H pre hpre
    have hfun :
        (fun pad : DetSchedule n =>
          p ((pre ++ pad).take H)) =
        (fun _ : DetSchedule n => p pre) := by
      funext pad
      rw [← hlen, List.take_append_length]
    rw [hfun]
    cases hp : p pre <;>
      simp [hp, allSchedules_length]
  rw [hmap]
  exact q19708SumIfCount
    (allSchedules n H) p (n ^ P)

private def q19708Paper_le_sweep (n : Nat) :
    lemma5PaperSweepHorizon n <=
      lemma5SweepHorizon n := by
  have h := lemma5iRetimedLastArmPadding n
  omega

private def q19708TraversalCurrent_padding
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (sweep pad : DetSchedule n)
    (hlen :
      sweep.length = lemma5SweepHorizon n) :
    q19708TraversalCurrentMaxBadB
        ring D (sweep ++ pad) =
      q19708TraversalCurrentMaxBadB
        ring D sweep := by
  unfold q19708TraversalCurrentMaxBadB
  have hle :
      lemma5PaperSweepHorizon n <=
        sweep.length := by
    rw [hlen]
    exact q19708Paper_le_sweep n
  rw [List.take_append_of_le_length hle]

private def q19708MidCurrent_padding
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (sweep pad : DetSchedule n)
    (hlen :
      sweep.length = lemma5SweepHorizon n) :
    q19708MidCurrentMaxBadB
        ring D (sweep ++ pad) =
      q19708MidCurrentMaxBadB
        ring D sweep := by
  unfold q19708MidCurrentMaxBadB
  have hle :
      lemma5PaperSweepHorizon n <=
        sweep.length := by
    rw [hlen]
    exact q19708Paper_le_sweep n
  rw [List.take_append_of_le_length hle]

private def q19708NeverLeaderless_step
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hcnz : neverLeaderless ring C)
    (e : Fin n) :
    neverLeaderless ring
      (pplStep ring C e) := by
  intro D hreach
  apply hcnz D
  have hone :
      PopulationProtocol.OneStep
        (PPL.protocol psi kappa) ring C
        (pplStep ring C e) := by
    exact ⟨e, rfl⟩
  exact
    PopulationProtocol.Reachable.trans
      (PopulationProtocol.OneStep.to_reachable hone)
      hreach

/-! ## Endpoint-retaining first-terminal bind -/

private def q19708TraversalAuxCount
    (hT :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (hlineage :
        SignalLineageOwnership
          (psi := psi) (kappa := kappa) ring)
      (fuel : Nat)
      (C : Config n psi kappa),
    (allSchedules n
        (lemma5SweepHorizon n + fuel)).countP
        (q19708RetimedTraversalBadAux
          ring C fuel) <=
      n ^ fuel *
        (n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n)) := by
  intro n psi kappa
  intro hn3 hpsi hkappa ring hlineage
  intro fuel
  induction fuel with
  | zero =>
      intro C
      cases hm : maxResetSignalB C with
      | false =>
          simp [q19708RetimedTraversalBadAux, hm]
      | true =>
          have hfun :
              q19708RetimedTraversalBadAux
                  ring C 0 =
                q19708TraversalCurrentMaxBadB
                  ring C := by
            funext word
            exact
              q19708TraversalAux_eq_currentMax
                ring C 0 word hm
          rw [hfun, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
          exact
            hT hn3 hpsi hkappa
              ring C hlineage hm
  | succ fuel ih =>
      intro C
      cases hm : maxResetSignalB C with
      | true =>
          have hfun :
              q19708RetimedTraversalBadAux
                  ring C (fuel + 1) =
                q19708TraversalCurrentMaxBadB
                  ring C := by
            funext word
            exact
              q19708TraversalAux_eq_currentMax
                ring C (fuel + 1) word hm
          rw [hfun]
          have hpad :=
            q19708CountP_prefixInvariant
              (n := n)
              (H := lemma5SweepHorizon n)
              (P := fuel + 1)
              (q19708TraversalCurrentMaxBadB
                ring C)
              (by
                intro sweep hsweep pad
                exact
                  q19708TraversalCurrent_padding
                    ring C sweep pad hsweep)
          rw [hpad]
          have hcur :=
            hT hn3 hpsi hkappa
              ring C hlineage hm
          calc
            (allSchedules n
                (lemma5SweepHorizon n)).countP
                  (q19708TraversalCurrentMaxBadB
                    ring C) *
                n ^ (fuel + 1) <=
              (n ^ (2 * n * n) *
                fixedWordMissCount
                  (lemma5ClockwiseSweepWord n)
                  (lemma5PaperSweepHorizon n)) *
                n ^ (fuel + 1) :=
              Nat.mul_le_mul_right
                (n ^ (fuel + 1)) hcur
            _ =
              n ^ (fuel + 1) *
                (n ^ (2 * n * n) *
                  fixedWordMissCount
                    (lemma5ClockwiseSweepWord n)
                    (lemma5PaperSweepHorizon n)) := by
              ac_rfl
      | false =>
          let B : Nat :=
            n ^ fuel *
              (n ^ (2 * n * n) *
                fixedWordMissCount
                  (lemma5ClockwiseSweepWord n)
                  (lemma5PaperSweepHorizon n))
          have hpoint :
              forall pre : DetSchedule n,
                pre ∈ allSchedules n 1 ->
                ((allSchedules n
                    (lemma5SweepHorizon n + fuel)).map
                    (fun suf => pre ++ suf)).countP
                    (q19708RetimedTraversalBadAux
                      ring C (fuel + 1)) <=
                  B := by
            intro pre hpre
            have hlen :=
              allSchedules_schedule_length
                n 1 pre hpre
            cases pre with
            | nil =>
                simp at hlen
            | cons e rest =>
                cases rest with
                | nil =>
                    rw [List.countP_map]
                    simpa [Function.comp_def,
                      q19708RetimedTraversalBadAux,
                      hm, B]
                      using
                        ih (pplStep ring C e)
                | cons e2 rest2 =>
                    simp at hlen
          calc
            (allSchedules n
                (lemma5SweepHorizon n +
                  (fuel + 1))).countP
                (q19708RetimedTraversalBadAux
                  ring C (fuel + 1)) =
              ((allSchedules n 1).map
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedTraversalBadAux
                      ring C (fuel + 1)))).sum := by
                rw [show
                    lemma5SweepHorizon n +
                        (fuel + 1) =
                      1 +
                        (lemma5SweepHorizon n +
                          fuel) by omega,
                  q19708AllSchedules_add,
                  List.countP_flatMap]
                try simp only [Function.comp_def]
            _ <=
              ((allSchedules n 1).map
                (fun _ => B)).sum :=
              q19708SumMapLe
                (allSchedules n 1)
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedTraversalBadAux
                      ring C (fuel + 1)))
                (fun _ => B)
                hpoint
            _ =
              (allSchedules n 1).length * B :=
              q19708SumMapConst
                (allSchedules n 1) B
            _ = n * B := by
              rw [allSchedules_length]
              simp
            _ =
              n ^ (fuel + 1) *
                (n ^ (2 * n * n) *
                  fixedWordMissCount
                    (lemma5ClockwiseSweepWord n)
                    (lemma5PaperSweepHorizon n)) := by
              dsimp [B]
              rw [Nat.pow_succ]
              ac_rfl

private def q19708MidAuxCount
    (hM :
      Lemma5iRetimedMidCurrentMaxSuffixBound) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (hclock : StoppedClockSuffixBoundsCorrected)
      (hmarked : ModeStoppedTreeTransfer)
      (hpredict : PredictableHostTails)
      (hhead : WLGHeadOffsetBounds)
      (hlottery : LotteryCountBounds)
      (fuel : Nat)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    (allSchedules n
        (lemma5SweepHorizon n + fuel)).countP
        (q19708RetimedMidClockBadAux
          ring C fuel) *
        2 ^ psi <=
      n ^ (lemma5SweepHorizon n + fuel) := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring hclock hmarked hpredict hhead hlottery
  intro fuel
  induction fuel with
  | zero =>
      intro C hcnz
      cases hm : maxResetSignalB C with
      | false =>
          simp [q19708RetimedMidClockBadAux, hm]
      | true =>
          have hfun :
              q19708RetimedMidClockBadAux
                  ring C 0 =
                q19708MidCurrentMaxBadB
                  ring C := by
            funext word
            exact
              q19708MidAux_eq_currentMax
                ring C 0 word hm
          rw [hfun]
          exact
            hM hn3 hpsi hkappa hnpow
              ring C hcnz
              hclock hmarked hpredict
              hhead hlottery hm
  | succ fuel ih =>
      intro C hcnz
      cases hm : maxResetSignalB C with
      | true =>
          have hfun :
              q19708RetimedMidClockBadAux
                  ring C (fuel + 1) =
                q19708MidCurrentMaxBadB
                  ring C := by
            funext word
            exact
              q19708MidAux_eq_currentMax
                ring C (fuel + 1) word hm
          rw [hfun]
          have hpad :=
            q19708CountP_prefixInvariant
              (n := n)
              (H := lemma5SweepHorizon n)
              (P := fuel + 1)
              (q19708MidCurrentMaxBadB
                ring C)
              (by
                intro sweep hsweep pad
                exact
                  q19708MidCurrent_padding
                    ring C sweep pad hsweep)
          rw [hpad]
          have hcur :=
            hM hn3 hpsi hkappa hnpow
              ring C hcnz
              hclock hmarked hpredict
              hhead hlottery hm
          calc
            ((allSchedules n
                (lemma5SweepHorizon n)).countP
                  (q19708MidCurrentMaxBadB
                    ring C) *
                n ^ (fuel + 1)) *
                2 ^ psi =
              n ^ (fuel + 1) *
                ((allSchedules n
                    (lemma5SweepHorizon n)).countP
                    (q19708MidCurrentMaxBadB
                      ring C) *
                  2 ^ psi) := by
              ac_rfl
            _ <=
              n ^ (fuel + 1) *
                n ^ lemma5SweepHorizon n :=
              Nat.mul_le_mul_left
                (n ^ (fuel + 1)) hcur
            _ =
              n ^
                ((fuel + 1) +
                  lemma5SweepHorizon n) := by
              first | (simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc]; done) | rw [Nat.pow_add]
            _ =
              n ^
                (lemma5SweepHorizon n +
                  (fuel + 1)) := by
              congr 1
              omega
      | false =>
          let B : Nat :=
            n ^ (lemma5SweepHorizon n + fuel)
          have hpoint :
              forall pre : DetSchedule n,
                pre ∈ allSchedules n 1 ->
                ((allSchedules n
                    (lemma5SweepHorizon n + fuel)).map
                    (fun suf => pre ++ suf)).countP
                    (q19708RetimedMidClockBadAux
                      ring C (fuel + 1)) *
                    2 ^ psi <=
                  B := by
            intro pre hpre
            have hlen :=
              allSchedules_schedule_length
                n 1 pre hpre
            cases pre with
            | nil =>
                simp at hlen
            | cons e rest =>
                cases rest with
                | nil =>
                    rw [List.countP_map]
                    have hcnz' :=
                      q19708NeverLeaderless_step
                        ring C hcnz e
                    simpa [Function.comp_def,
                      q19708RetimedMidClockBadAux,
                      hm, B]
                      using
                        ih (pplStep ring C e) hcnz'
                | cons e2 rest2 =>
                    simp at hlen
          calc
            (allSchedules n
                (lemma5SweepHorizon n +
                  (fuel + 1))).countP
                (q19708RetimedMidClockBadAux
                  ring C (fuel + 1)) *
                2 ^ psi =
              ((allSchedules n 1).map
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedMidClockBadAux
                      ring C (fuel + 1)))).sum *
                2 ^ psi := by
              rw [show
                  lemma5SweepHorizon n +
                      (fuel + 1) =
                    1 +
                      (lemma5SweepHorizon n +
                        fuel) by omega,
                q19708AllSchedules_add,
                List.countP_flatMap]
              try simp only [Function.comp_def]
            _ =
              ((allSchedules n 1).map
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedMidClockBadAux
                      ring C (fuel + 1)) *
                    2 ^ psi)).sum :=
              q19708SumMapMulRight
                (allSchedules n 1)
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedMidClockBadAux
                      ring C (fuel + 1)))
                (2 ^ psi)
            _ <=
              ((allSchedules n 1).map
                (fun _ => B)).sum :=
              q19708SumMapLe
                (allSchedules n 1)
                (fun pre =>
                  ((allSchedules n
                      (lemma5SweepHorizon n + fuel)).map
                      (fun suf => pre ++ suf)).countP
                    (q19708RetimedMidClockBadAux
                      ring C (fuel + 1)) *
                    2 ^ psi)
                (fun _ => B)
                hpoint
            _ =
              (allSchedules n 1).length * B :=
              q19708SumMapConst
                (allSchedules n 1) B
            _ = n * B := by
              rw [allSchedules_length]
              simp
            _ =
              n ^
                (lemma5SweepHorizon n +
                  (fuel + 1)) := by
              dsimp [B]
              rw [show
                  lemma5SweepHorizon n +
                      (fuel + 1) =
                    (lemma5SweepHorizon n +
                      fuel) + 1 by omega,
                Nat.pow_succ]
              ac_rfl

private def q19708Horizon_comm (n : Nat) :
    lemma5iHorizon n =
      lemma5SweepHorizon n +
        lemma5ArmHorizon n := by
  unfold lemma5iHorizon
  omega

private def q19708Outer_eq_horizon (n : Nat) :
    (lemma5ArmHorizon n + 2 * n * n) +
        lemma5PaperSweepHorizon n =
      lemma5iHorizon n := by
  calc
    (lemma5ArmHorizon n + 2 * n * n) +
        lemma5PaperSweepHorizon n =
      lemma5ArmHorizon n +
        (lemma5PaperSweepHorizon n +
          2 * n * n) := by
        omega
    _ =
      lemma5ArmHorizon n +
        lemma5SweepHorizon n := by
        rw [lemma5iRetimedLastArmPadding]
    _ = lemma5iHorizon n := by
        rfl

private def q19708TraversalFirstMaxCount
    (hT :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    lemma5iRetimedTraversalFailureCount ring C <=
      n ^ (lemma5ArmHorizon n + 2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n) := by
  intro n psi kappa
  intro hn3 hpsi hkappa ring C hlineage
  have haux :=
    q19708TraversalAuxCount
      hT hn3 hpsi hkappa
      ring hlineage
      (lemma5ArmHorizon n) C
  unfold lemma5iRetimedTraversalFailureCount
  rw [q19708Horizon_comm]
  rw [q19708TraversalBadB_fun_eq]
  calc
    (allSchedules n
        (lemma5SweepHorizon n +
          lemma5ArmHorizon n)).countP
        (q19708RetimedTraversalBadAux
          ring C (lemma5ArmHorizon n)) <=
      n ^ lemma5ArmHorizon n *
        (n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n)) :=
      haux
    _ =
      n ^ (lemma5ArmHorizon n + 2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n) := by
      first | (simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc]; done) | rw [Nat.pow_add]
      try ac_rfl

private def q19708MidFirstMaxCount
    (hM :
      Lemma5iRetimedMidCurrentMaxSuffixBound) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    lemma5iRetimedMidClockFailureCount ring C *
        2 ^ psi <=
      n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C hcnz
  intro hclock hmarked hpredict hhead hlottery
  have haux :=
    q19708MidAuxCount
      hM hn3 hpsi hkappa hnpow
      ring hclock hmarked hpredict
      hhead hlottery
      (lemma5ArmHorizon n) C hcnz
  unfold lemma5iRetimedMidClockFailureCount
  rw [q19708Horizon_comm]
  rw [q19708MidBadB_fun_eq]
  exact haux

/--
Endpoint-retaining first-terminal/Kraft bind.

The recursion follows the actual physical child while maxResetSignalB is
false.  At the first current-max endpoint it consumes the state-rooted
8*n^2 suffix estimate.  The unspent arm coordinates are then pure counting
padding after that continuation; no fixed-arm endpoint substitution occurs.
-/
theorem lemma5iSweepMidCountRetimed_of_currentMax
    (hT :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjection)
    (hM :
      Lemma5iRetimedMidCurrentMaxSuffixBound) :
    Lemma5iSweepMidCountRetimed := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery

  have hTraversal :=
    q19708TraversalFirstMaxCount
      hT hn3 hpsi hkappa
      ring C hlineage

  have hMid :=
    q19708MidFirstMaxCount
      hM hn3 hpsi hkappa hnpow
      ring C hcnz
      hclock hmarked hpredict hhead hlottery

  constructor
  · have hscaled :=
      Nat.mul_le_mul_right
        (2 ^ (2 * n)) hTraversal
    have hmiss :=
      lemma5ClockwiseSweepWord_miss_scaled n
    have hmissPad :=
      Nat.mul_le_mul_left
        (n ^
          (lemma5ArmHorizon n +
            2 * n * n))
        hmiss
    have hnscale :
        n <= 2 ^ (2 * n) :=
      nat_le_two_pow_two_mul_sweepMid n
    calc
      n * lemma5iRetimedTraversalFailureCount ring C =
          lemma5iRetimedTraversalFailureCount ring C * n := by
        ac_rfl
      _ <=
          lemma5iRetimedTraversalFailureCount ring C *
            2 ^ (2 * n) :=
        Nat.mul_le_mul_left
          (lemma5iRetimedTraversalFailureCount ring C)
          hnscale
      _ <=
          (n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n)) *
            2 ^ (2 * n) :=
        hscaled
      _ =
          n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            (fixedWordMissCount
                (lemma5ClockwiseSweepWord n)
                (lemma5PaperSweepHorizon n) *
              2 ^ (2 * n)) := by
        ac_rfl
      _ <=
          n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            n ^ lemma5PaperSweepHorizon n :=
        hmissPad
      _ =
          n ^
            ((lemma5ArmHorizon n +
                2 * n * n) +
              lemma5PaperSweepHorizon n) := by
        first | (simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc]; done) | rw [Nat.pow_add]
      _ = n ^ lemma5iHorizon n := by
        rw [q19708Outer_eq_horizon]
      _ <= 2 * n ^ lemma5iHorizon n := by
        omega

  · calc
      n * lemma5iRetimedMidClockFailureCount ring C =
          lemma5iRetimedMidClockFailureCount ring C * n := by
        ac_rfl
      _ <=
          lemma5iRetimedMidClockFailureCount ring C *
            2 ^ psi :=
        Nat.mul_le_mul_left
          (lemma5iRetimedMidClockFailureCount ring C)
          hnpow
      _ <= n ^ lemma5iHorizon n :=
        hMid
      _ <= 2 * n ^ lemma5iHorizon n := by
        omega

/-! ## Current-max mid projection -/

/--
The new unconditional theorem on main closes the two literal one-step leaves,
but its exported word projection is still fixed-arm shaped: it requires a
prefix pre of length lemma5ArmHorizon n and starts its paper window at
runPPL ring C pre.

The proof in Lemma5iMidLatestResetProjection is already physically rooted at
that endpoint after the prefix is peeled off, and its historical arm witness
is not used after extraction.  What is not public is exactly this re-rooted
word statement for an arbitrary current configuration D.  No new probability
estimate or transition law is hidden here.
-/
def Lemma5iRetimedMidCurrentMaxWordProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    neverLeaderless ring D ->
    StoppedClockSuffixBoundsCorrected ->
    maxResetSignalB D = true ->
    forall sweep : DetSchedule n,
      sweep ∈ allSchedules n
        (lemma5PaperSweepHorizon n) ->
      q19708MidCurrentPaperBadB
          ring D sweep = true ->
      And
        (3 <= psi)
        (And
          (psi <= n)
          (exists x : Fin n,
            lemma5iMidAgentBadB
              ring D x sweep = true))

private def q19708MidAnyPred {A : Type} :
    List (A -> Bool) -> A -> Bool
  | [], _ => false
  | p :: ps, x =>
      p x || q19708MidAnyPred ps x

private def q19708MidAnyPred_true_of_mem
    {A : Type}
    (ps : List (A -> Bool))
    (p : A -> Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    q19708MidAnyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [q19708MidAnyPred, hp]
      · have ht := ih hq
        simp [q19708MidAnyPred, ht]

private def q19708MidCountP_mono_mem
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      forall x,
        x ∈ xs ->
        p x = true ->
        q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          forall y,
            y ∈ xs ->
            p y = true ->
            q y = true := by
        intro y hy
        exact hpq y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;>
            simp_all <;>
            omega
      | true =>
          have hq :
              q x = true :=
            hpq x (by simp) hp
          simpa [hp, hq] using hi

private def q19708MidCountP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

private def q19708MidCountP_anyPred_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A -> Bool)) :
    xs.countP (q19708MidAnyPred ps) <=
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [q19708MidAnyPred]
  | cons p ps ih =>
      calc
        xs.countP
            (q19708MidAnyPred (p :: ps)) =
          xs.countP
            (fun x =>
              p x || q19708MidAnyPred ps x) := by
          rfl
        _ <=
          xs.countP p +
            xs.countP (q19708MidAnyPred ps) :=
          q19708MidCountP_or_le_add
            xs p (q19708MidAnyPred ps)
        _ <=
          xs.countP p +
            (ps.map
              (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
          ((p :: ps).map
            (fun q => xs.countP q)).sum := by
          simp

private def q19708MidNatLeTwoPowSelf (n : Nat) :
    n <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ n :=
        Nat.pow_pos (by omega)
      omega

private def q19708MidCurrentPaperFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa) : Nat :=
  (allSchedules n
    (lemma5PaperSweepHorizon n)).countP
      (q19708MidCurrentPaperBadB ring D)

private def q19708MidCurrentMaxPaperCount
    (hprojection :
      Lemma5iRetimedMidCurrentMaxWordProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    neverLeaderless ring D ->
    StoppedClockSuffixBoundsCorrected ->
    WLGHeadOffsetBounds ->
    maxResetSignalB D = true ->
    q19708MidCurrentPaperFailureCount
        ring D *
        2 ^ psi <=
      n ^ lemma5PaperSweepHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hcnz hclock hoffset hmax

  let T : Nat :=
    lemma5PaperSweepHorizon n
  let words : List (DetSchedule n) :=
    allSchedules n T
  let bad : DetSchedule n -> Bool :=
    q19708MidCurrentPaperBadB ring D
  let agentPred :
      Fin n -> DetSchedule n -> Bool :=
    fun x =>
      lemma5iMidAgentBadB ring D x
  let agentCount : Fin n -> Nat :=
    fun x => words.countP (agentPred x)
  let preds :
      List (DetSchedule n -> Bool) :=
    List.ofFn agentPred
  let F : Nat :=
    q19708MidCurrentPaperFailureCount
      ring D

  by_cases hex :
      exists sweep : DetSchedule n,
        And (sweep ∈ words)
          (bad sweep = true)
  · obtain ⟨w0, hw0mem, hw0bad⟩ := hex

    have hw0mem' :
        w0 ∈ allSchedules n
          (lemma5PaperSweepHorizon n) := by
      simpa [words, T] using hw0mem

    have hp0 :=
      hprojection
        hn3 hpsi hkappa hnpow
        ring D hcnz hclock hmax
        w0 hw0mem'
        (by simpa [bad] using hw0bad)

    have hpsi3 : 3 <= psi :=
      hp0.1
    have hpsin : psi <= n :=
      hp0.2.1

    have hbadToAny :
        forall sweep : DetSchedule n,
          sweep ∈ words ->
          bad sweep = true ->
          q19708MidAnyPred preds sweep = true := by
      intro sweep hsweep hbad
      have hsweep' :
          sweep ∈ allSchedules n
            (lemma5PaperSweepHorizon n) := by
        simpa [words, T] using hsweep
      obtain ⟨x, hx⟩ :=
        (hprojection
          hn3 hpsi hkappa hnpow
          ring D hcnz hclock hmax
          sweep hsweep'
          (by simpa [bad] using hbad)).2.2
      apply
        q19708MidAnyPred_true_of_mem
          preds (agentPred x) sweep
      · dsimp [preds]
        rw [List.mem_ofFn]
        exact ⟨x, rfl⟩
      · simpa [agentPred] using hx

    have hunion :
        F <=
          (List.ofFn agentCount).sum := by
      calc
        F = words.countP bad := by
          rfl
        _ <=
          words.countP
            (q19708MidAnyPred preds) :=
          q19708MidCountP_mono_mem
            words bad
            (q19708MidAnyPred preds)
            (by
              intro sweep hsweep hbad
              exact
                hbadToAny
                  sweep hsweep hbad)
        _ <=
          (preds.map
            (fun p =>
              words.countP p)).sum :=
          q19708MidCountP_anyPred_le_sum
            words preds
        _ =
          (List.ofFn agentCount).sum := by
          dsimp [preds, agentCount, agentPred]
          rw [List.map_ofFn]
          rfl

    let common : Nat :=
      2 * n * 2 ^ psi

    have htwoN :
        2 <= 2 ^ n := by
      have hn1 : 1 <= n := by
        omega
      have h :=
        Nat.pow_le_pow_right
          (by omega : 0 < 2) hn1
      simpa using h

    have hnSelf :
        n <= 2 ^ n :=
      q19708MidNatLeTwoPowSelf n

    have hpsiPowN :
        2 ^ psi <= 2 ^ n :=
      Nat.pow_le_pow_right
        (by omega : 0 < 2) hpsin

    have hcommonEncounter :
        common <= 2 ^ (4 * n) := by
      have hm :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            htwoN hnSelf)
          hpsiPowN
      calc
        common <=
          (2 ^ n * 2 ^ n) *
            2 ^ n := by
          simpa [common,
            Nat.mul_assoc] using hm
        _ = 2 ^ (3 * n) := by
          rw [← Nat.pow_add,
            ← Nat.pow_add]
          congr 1
          omega
        _ <= 2 ^ (4 * n) :=
          Nat.pow_le_pow_right
            (by omega : 0 < 2)
            (by omega)

    have htwoPsi :
        2 <= 2 ^ psi := by
      have hp1 : 1 <= psi := by
        omega
      have h :=
        Nat.pow_le_pow_right
          (by omega : 0 < 2) hp1
      simpa using h

    have hcommonLottery :
        common <= 2 ^ (9 * psi) := by
      have hm :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            htwoPsi hnpow)
          (Nat.le_refl (2 ^ psi))
      calc
        common <=
          (2 ^ psi * 2 ^ psi) *
            2 ^ psi := by
          simpa [common,
            Nat.mul_assoc] using hm
        _ = 2 ^ (3 * psi) := by
          rw [← Nat.pow_add,
            ← Nat.pow_add]
          congr 1
          omega
        _ <= 2 ^ (9 * psi) :=
          Nat.pow_le_pow_right
            (by omega : 0 < 2)
            (by omega)

    have hagent :
        forall x : Fin n,
          common * agentCount x <=
            2 * n ^ T := by
      intro x
      let enc : Nat :=
        words.countP
          (lemma5iMidEncounterAgentBadB
            ring x)
      let lot : Nat :=
        words.countP
          (lemma5iMidLotteryAgentBadB
            ring D x)

      have hsplit :
          agentCount x <= enc + lot := by
        dsimp [agentCount, agentPred,
          enc, lot]
        exact
          q19708MidCountP_or_le_add
            words
            (lemma5iMidEncounterAgentBadB
              ring x)
            (lemma5iMidLotteryAgentBadB
              ring D x)

      have henc0 :=
        lemma5iMidEncounterAgentCount
          hn3 ring x
      have henc :
          common * enc <= n ^ T := by
        calc
          common * enc <=
            2 ^ (4 * n) * enc :=
              Nat.mul_le_mul_right
                enc hcommonEncounter
          _ =
            2 ^ (4 * n) *
              lemma5iMidEncounterAgentFailureCount
                ring x := by
              dsimp [enc, words, T]
              rfl
          _ <=
            n ^ lemma5PaperSweepHorizon n :=
              henc0
          _ = n ^ T := by
              rfl

      have hlot0 :=
        lemma5iMidLotteryAgentCount
          hn3 hpsi ring D x hoffset
      have hlot :
          common * lot <= n ^ T := by
        calc
          common * lot <=
            2 ^ (9 * psi) * lot :=
              Nat.mul_le_mul_right
                lot hcommonLottery
          _ =
            2 ^ (9 * psi) *
              lemma5iMidLotteryAgentFailureCount
                ring D x := by
              dsimp [lot, words, T]
              rfl
          _ <=
            n ^ lemma5PaperSweepHorizon n :=
              hlot0
          _ = n ^ T := by
              rfl

      calc
        common * agentCount x <=
          common * (enc + lot) :=
            Nat.mul_le_mul_left
              common hsplit
        _ =
          common * enc +
            common * lot := by
            rw [Nat.mul_add]
        _ <=
          n ^ T + n ^ T :=
            Nat.add_le_add henc hlot
        _ = 2 * n ^ T := by
            omega

    have hsum :
        (List.ofFn
          (fun x : Fin n =>
            common * agentCount x)).sum <=
        (List.ofFn
          (fun _ : Fin n =>
            2 * n ^ T)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_le
        (fun x : Fin n =>
          common * agentCount x)
        (fun _ : Fin n =>
          2 * n ^ T)
        hagent

    have hsum' :
        common *
            (List.ofFn agentCount).sum <=
          n * (2 * n ^ T) := by
      calc
        common *
            (List.ofFn agentCount).sum =
          (List.ofFn
            (fun x : Fin n =>
              common * agentCount x)).sum :=
          (FiniteUniformStoppingTree.ofFn_sum_mul_left
            common agentCount).symm
        _ <=
          (List.ofFn
            (fun _ : Fin n =>
              2 * n ^ T)).sum :=
          hsum
        _ =
          n * (2 * n ^ T) :=
          FiniteUniformStoppingTree.ofFn_sum_const
            n (2 * n ^ T)

    have hscaledF :
        common * F <=
          n * (2 * n ^ T) :=
      Nat.le_trans
        (Nat.mul_le_mul_left
          common hunion)
        hsum'

    have hcancellable :
        (2 * n) * (2 ^ psi * F) <=
          (2 * n) * n ^ T := by
      calc
        (2 * n) * (2 ^ psi * F) =
          common * F := by
            dsimp [common]
            ac_rfl
        _ <=
          n * (2 * n ^ T) :=
            hscaledF
        _ =
          (2 * n) * n ^ T := by
            ac_rfl

    have hfinal :
        2 ^ psi * F <= n ^ T :=
      Nat.le_of_mul_le_mul_left
        hcancellable
        (by omega)

    simpa [F, T, Nat.mul_comm]
      using hfinal

  · have hzero :
        F = 0 := by
      dsimp [F]
      unfold q19708MidCurrentPaperFailureCount
      apply List.countP_eq_zero.mpr
      intro sweep hsweep hbad
      have hmem :
          sweep ∈ words := by
        simpa [words, T] using hsweep
      exact
        hex
          ⟨sweep,
            And.intro hmem
              (by simpa [bad] using hbad)⟩
    have hz : q19708MidCurrentPaperFailureCount ring D = 0 := hzero
    rw [hz]
    simp

/--
The fixed-arm unconditional theorem does not by itself imply this arbitrary-D
statement: its exported type still requires an exact arm prefix.  The single
missing interface is Lemma5iRetimedMidCurrentMaxWordProjection above.  From
that re-rooted word fact, all scheduler counting is already on main and the
current-max 8*n^2 suffix bound follows.
-/
theorem lemma5iRetimedMidCurrentMaxSuffixBound_proved
    (hprojection :
      Lemma5iRetimedMidCurrentMaxWordProjection) :
    Lemma5iRetimedMidCurrentMaxSuffixBound := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D
  intro hcnz hclock _hmarked
  intro _hpredict hhead _hlottery
  intro hmax

  have hpaper :=
    q19708MidCurrentMaxPaperCount
      hprojection
      hn3 hpsi hkappa hnpow
      ring D hcnz hclock hhead hmax

  have hpad0 :=
    q19708CountP_take_pad
      (n := n)
      (H := lemma5PaperSweepHorizon n)
      (P := 2 * n * n)
      (q19708MidCurrentPaperBadB ring D)

  have hpad :
      (allSchedules n
          (lemma5SweepHorizon n)).countP
          (q19708MidCurrentMaxBadB ring D) =
        q19708MidCurrentPaperFailureCount
            ring D *
          n ^ (2 * n * n) := by
    change
      (allSchedules n
          (lemma5SweepHorizon n)).countP
          (fun suffix =>
            q19708MidCurrentPaperBadB
              ring D
              (suffix.take
                (lemma5PaperSweepHorizon n))) =
        q19708MidCurrentPaperFailureCount
            ring D *
          n ^ (2 * n * n)
    rw [← lemma5iRetimedLastArmPadding n]
    simpa [q19708MidCurrentPaperFailureCount]
      using hpad0

  change
    (allSchedules n
        (lemma5SweepHorizon n)).countP
        (q19708MidCurrentMaxBadB ring D) *
        2 ^ psi <=
      n ^ lemma5SweepHorizon n

  rw [hpad]
  calc
    (q19708MidCurrentPaperFailureCount
        ring D *
        n ^ (2 * n * n)) *
        2 ^ psi =
      n ^ (2 * n * n) *
        (q19708MidCurrentPaperFailureCount
          ring D * 2 ^ psi) := by
        ac_rfl
    _ <=
      n ^ (2 * n * n) *
        n ^ lemma5PaperSweepHorizon n :=
      Nat.mul_le_mul_left
        (n ^ (2 * n * n))
        hpaper
    _ =
      n ^
        (2 * n * n +
          lemma5PaperSweepHorizon n) := by
        first | (simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc]; done) | rw [Nat.pow_add]
    _ = n ^ lemma5SweepHorizon n := by
      have h :=
        lemma5iRetimedLastArmPadding n
      congr 1
      omega

/-! ## Relation to the fixed-arm traversal interface -/

private def q19708ArmPrefix_append
    {n : Nat}
    (pre tail : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n) :
    lemma5iArmPrefix (pre ++ tail) = pre := by
  unfold lemma5iArmPrefix
  rw [← hpre]
  exact List.take_append_length

private def q19708PaperSweep_append
    {n : Nat}
    (pre tail : DetSchedule n)
    (hpre :
      pre.length = lemma5ArmHorizon n) :
    lemma5iPaperSweepSuffix (pre ++ tail) =
      tail.take (lemma5PaperSweepHorizon n) := by
  unfold lemma5iPaperSweepSuffix
  have hdrop :
      (pre ++ tail).drop
          (lemma5ArmHorizon n) =
        tail := by
    rw [← hpre]
    exact List.drop_append_length
  rw [hdrop]

private def q19708ReachesAux_of_final
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hfinal :
      good (runPPL ring C word) = true) :
    reachesAux ring good C word = true := by
  induction word generalizing C with
  | nil =>
      simpa [reachesAux, runPPL,
        runPopulationSchedule] using hfinal
  | cons e rest ih =>
      have htail :
          good
            (runPPL ring
              (pplStep ring C e) rest) =
            true := by
        simpa [runPPL,
          runPopulationSchedule,
          pplStep] using hfinal
      have ht :=
        ih (C := pplStep ring C e) htail
      simp [reachesAux, ht]

/--
Classification: the current-max traversal interface is a strengthening of
Lemma5iTraversalLiveSuffixPhysicalProjection.

It implies the fixed-arm theorem by taking D = runPPL ring C pre.  The live
endpoint hypothesis makes the historical arm test true, and the old suffix
event is then literally the current-max suffix event.  The converse is not
available: the fixed-arm interface only constrains configurations appearing
after an exact lemma5ArmHorizon prefix, whereas the current-max interface is
uniform over arbitrary current D with maxResetSignalB D = true.
-/
theorem lemma5iTraversalLiveSuffixPhysicalProjection_of_currentMax
    (hT :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjection) :
    Lemma5iTraversalLiveSuffixPhysicalProjection := by
  intro n psi kappa
  intro hn3 hpsi hkappa
  intro ring C hlineage
  intro pre hpre hmax

  let D : Config n psi kappa :=
    runPPL ring C pre

  have hpreLen :=
    allSchedules_schedule_length
      n (lemma5ArmHorizon n)
      pre hpre

  have hmaxD :
      maxResetSignalB D = true := by
    simpa [D] using hmax

  have harm :
      reachesAux ring maxResetSignalB
        C pre = true := by
    exact
      q19708ReachesAux_of_final
        ring maxResetSignalB C pre hmax

  have hfun :
      (fun suffix : DetSchedule n =>
        lemma5iTraversalLiveBadB
          ring C (pre ++ suffix)) =
      q19708TraversalCurrentMaxBadB
        ring D := by
    funext suffix
    unfold lemma5iTraversalLiveBadB
      q19708TraversalCurrentMaxBadB
    dsimp only
    rw [q19708ArmPrefix_append
          pre suffix hpreLen]
    rw [q19708PaperSweep_append
          pre suffix hpreLen]
    change
      (reachesAux ring maxResetSignalB C pre &&
        maxResetSignalB D &&
        !allClockResetsSeenB ring D
          (suffix.take
            (lemma5PaperSweepHorizon n))) =
      (!allClockResetsSeenB ring D
        (suffix.take
          (lemma5PaperSweepHorizon n)))
    rw [harm, hmaxD]
    rfl

  unfold lemma5iTraversalLiveSuffixFailureCount
  rw [List.countP_map]
  simp only [Function.comp_def]
  rw [hfun]
  exact
    hT hn3 hpsi hkappa
      ring D hlineage hmaxD

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_of_currentMax
#print axioms PPL.Modes.Lemma5.lemma5iRetimedMidCurrentMaxSuffixBound_proved
#print axioms PPL.Modes.Lemma5.lemma5iTraversalLiveSuffixPhysicalProjection_of_currentMax
