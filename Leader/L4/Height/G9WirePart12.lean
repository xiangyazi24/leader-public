import Leader.L4.Height.G9WirePart11
set_option Elab.async false
set_option pp.fullNames true

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PackedDisplay

open Classical
open L4.Compiler.Native
open PhysicalCustody
open BStarH6WordChart BStarAcquireAnchors BStarCycleGeometry
open BStarEpochLift BStarPhysicalCoset BStarPhysicalLiftAlignment BStarPhysicalLegitimate
open BStarGrantWriterHistory

noncomputable def packedTraceCount {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) (start : Fin n → Nat) (w : List (Fin n))
    (i : Fin (headers g)) : Nat :=
  traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
    (((g.u ++ g.v) ++ g.past) ++ w) (atIndex g.hh i).val

/-- The display trial begins at the actual stopped tape. Its counts extend
the original epoch, and its opening is the first aligned frontier beyond
the recorded upper bound on the stopped counts. -/
def packedOrigin {s n : Nat} (hn : 4 ≤ n) (hs : 6 ≤ s) :
    DisplayOrigin (packedData s n hn hs) :=
  fun j z _ opening level =>
    let g := extendWitness j.2 z.1
    let hist := (g.u ++ g.v) ++ g.past
    ∃ (start : Fin n → Nat) (G : Nat),
      opening = frontier G ∧
      (∀ i, traceCount (show 0 < 2 by decide) g.base g.initial g.hh start hist i ≤ G) ∧
      (∀ w i, level w i = packedTraceCount g start w i) ∧
      ∀ w : List (Fin n),
        let tape := hist ++ w
        let ticks := traceCount (show 0 < 2 by decide) g.base g.initial g.hh start tape
        RepresentsCoset (show 0 < 2 by decide) g.base (rawRun g.initial tape)
          (modulus (radWidth s) / 2) ticks ∧ Coherent g.hh ticks

/-- The physical trace and the chart lift agree after every raw mark. -/
theorem packed_trace_compatibility {s n : Nat} (hn : 4 ≤ n) (hs : 6 ≤ s) :
    DisplayTraceCompatibility (packedData s n hn hs) (packedOrigin hn hs) := by
  unfold DisplayTraceCompatibility
  intro j z _ opening level hz hOrigin
  let D := packedData s n hn hs
  let g := extendWitness j.2 z.1
  let hist := (g.u ++ g.v) ++ g.past
  let x := rawRun j.1 z.1
  have hHere : rawRun g.initial hist = x := g.here
  obtain ⟨start, _, _, _, hLevel, hRepr⟩ := hOrigin
  have hLevelEq (w : List (Fin n)) : level w = packedTraceCount g start w :=
    funext (hLevel w)
  constructor
  · obtain ⟨hRep, hCoherent⟩ := hRepr []
    let ticks := traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
      (hist ++ ([] : List (Fin n)))
    have hSame : rawRun g.initial (hist ++ ([] : List (Fin n))) = x :=
      (congrArg (rawRun g.initial) (List.append_nil hist)).trans hHere
    have hRep' : RepresentsCoset (show 0 < 2 by decide) g.base x
        (modulus (radWidth s) / 2) ticks :=
      Eq.mp (congrArg (fun y : Raw s n =>
        RepresentsCoset (show 0 < 2 by decide) g.base y (modulus (radWidth s) / 2) ticks)
        hSame) hRep
    change LegitCoset (modulus (radWidth s)) (total_pos (oldH6 (rows s) g.base) g.hh)
      ⟨literalClockCfg g.hh x, level []⟩
    rw [hLevelEq []]
    exact literal_legitCoset (show 0 < 2 by decide) g.hh ticks hRep' hCoherent hz.2.1 hz.2.2
  · intro w e
    let C := D.clock j
    let y := runWord C.next z w
    have hTape : y.1 = z.1 ++ w := chart_state_tape j.2 hn hs z w
    have hOld : rawRun g.initial (hist ++ w) = rawRun j.1 y.1 := by
      rw [hTape]
      calc
        rawRun g.initial (hist ++ w) = rawRun (rawRun g.initial hist) w :=
          BStarResetSchedule.run_append (rawNext s) g.initial hist w
        _ = rawRun x w := congrArg (fun a => rawRun a w) hHere
        _ = rawRun j.1 (z.1 ++ w) :=
          (BStarResetSchedule.run_append (rawNext s) j.1 z.1 w).symm
    have hPub (i : Fin (headers g)) :
        (∃ b, C.act y e = some (i,b)) ↔
          e = (atIndex g.hh i).val ∧
            ¬ NoPublication (show 0 < 2 by decide) (rawRun g.initial (hist ++ w)) e e := by
      rw [hOld]
      exact chooseMark_matches j.2 hn hs y.1 e i
    dsimp only
    rw [hLevelEq (w ++ [e]), hLevelEq w]
    have hTapeAppend : (hist ++ w) ++ [e] = hist ++ (w ++ [e]) :=
      List.append_assoc hist w [e]
    cases ha : C.act y e with
    | none =>
        simp only [ha] at hPub
        have hStep := literal_traceCount_snoc (show 0 < 2 by decide)
          g.base g.initial g.hh start (hist ++ w) e none hPub
        rw [hTapeAppend] at hStep
        exact hStep
    | some p =>
        obtain ⟨i, b⟩ := p
        simp only [ha] at hPub
        have hStep := literal_traceCount_snoc (show 0 < 2 by decide)
          g.base g.initial g.hh start (hist ++ w) e (some (i, b)) hPub
        rw [hTapeAppend] at hStep
        change packedTraceCount g start (w ++ [e]) =
          (activate (heightMod (radWidth s)) (modulus (radWidth s))
            (total_pos (oldH6 (rows s) g.base) g.hh)
            ⟨literalClockCfg g.hh (rawRun g.initial (hist ++ w)),
              packedTraceCount g start w⟩ i b).lift at hStep
        rw [hOld] at hStep
        have hCfg : C.cfg y = literalClockCfg g.hh (rawRun j.1 y.1) := rfl
        change packedTraceCount g start (w ++ [e]) =
          (activate (heightMod D.r) (modulus D.r) (D.hm j)
            ⟨C.cfg y, packedTraceCount g start w⟩ i b).lift
        rw [hCfg]
        exact hStep

theorem display_count_transport {n : Nat} (bad miss : List (Fin n) → Prop)
    (t : Nat) {badDec : ∀ w, Decidable (bad w)} {missDec : ∀ w, Decidable (miss w)}
    (h : 4 * wordSum (fun w => @ite Nat (bad w) (badDec w) 1 0) t ≤
      n ^ t + 4 * wordSum (fun w => @ite Nat (miss w) (missDec w) 1 0) t) :
    4 * failureCount bad t ≤ n ^ t + 4 * failureCount miss t := by
  have count (event : List (Fin n) → Prop) (dec : ∀ w, Decidable (event w)) :
      failureCount event t = wordSum (fun w => @ite Nat (event w) (dec w) 1 0) t := by
    unfold failureCount
    apply wordSum_congr_fun
    intro w
    by_cases hw : event w
    · simp only [if_pos hw]
    · simp only [if_neg hw]
  rw [count bad badDec, count miss missDec]
  exact h

theorem packed_display_deadline_formula {s n : Nat} (hn : 4 ≤ n) (hs : 6 ≤ s)
    (j : Epoch s n) (budget : Nat) :
    (packedData s n hn hs).deadline budget j =
      2 ^ 29 * (2 ^ (5 * budget + 34) * n * radWidth s) * headers j.2 := rfl

/-- Adapt the physical all-site deadline split to trials indexed by the
chart's finite header enumeration. -/
theorem packed_trial {s n : Nat} (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = AllSizeProtocol.ell (AllSizeProtocol.ell n))
    (hQuiet : ClockDisplaySpec.RawLegitOfQuiet)
    (hTrial : ClockDisplaySpec.RawDisplayTrial) :
    DotRawDisplay (packedData s n hn hs) (by omega) (2^32) (packedOrigin hn hs) := by
  classical
  let D := packedData s n hn hs
  change ∀ (j : Epoch s n) (z : TapeState j.2), Recover.Chain.LgSet (chartClock j.2 hn hs) z →
    Nonempty (RawDisplayTrial D (by omega) (2^32) (packedOrigin hn hs) j z)
  intro j z hz
  let x : Raw s n := rawRun j.1 z.1
  let g : CustodyWitness x := extendWitness j.2 z.1
  have hLegit := hQuiet g hz.1 hz.2.1 hz.2.2
  obtain ⟨start, lo, G, opening, cap, hOpening, hCap, hDepth, hRepr, hLower, hUpper, hSplit⟩ :=
    hTrial hn hs ha g hLegit
  let levels := packedTraceCount g start
  refine ⟨{
    lo := lo
    opening := opening
    level := levels
    historical := ⟨start, G, hOpening, hUpper, fun _ _ => rfl, hRepr⟩
    floor := fun i => by
      simpa only [levels, packedTraceCount, List.append_nil] using hLower (atIndex g.hh i)
    depth := by
      change opening + 32 * (2 ^ 19 * headers g) + 1 ≤
        lo + (headers g + 233 + 32 * (2 ^ 19 * headers g))
      rw [hCap] at hDepth
      exact hDepth
    split := ?_
  }⟩
  let hist := (g.u ++ g.v) ++ g.past
  let missHeader := fun (w : List (Fin n)) => ∃ i : Header (oldH6 (rows s) g.base),
    traceCount (show 0 < 2 by decide) g.base g.initial g.hh start (hist ++ w) i.val ≤ cap
  let missIndex := fun (w : List (Fin n)) => ∃ i, levels w i ≤ opening + 32 * (2 ^ 19 * D.m j)
  let physicallyBad := fun (w : List (Fin n)) =>
    ¬ ClockDisplaySpec.PermanentReference (rawRun x w)
  let chartBad := fun (w : List (Fin n)) =>
    ¬ D.display (by omega) (runWord (D.next (by omega)) x w)
  have hMiss : missHeader = missIndex := by
    funext w
    apply propext
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨BStarCycleGeometry.index g.hh i, ?_⟩
      change traceCount (show 0 < 2 by decide) g.base g.initial g.hh start
        (hist ++ w) (atIndex g.hh (BStarCycleGeometry.index g.hh i)).val ≤
        opening + 32 * (2 ^ 19 * headers g)
      simpa only [BStarCycleGeometry.atIndex_index, hCap] using hi
    · rintro ⟨i, hi⟩
      refine ⟨atIndex g.hh i, ?_⟩
      change packedTraceCount g start w i ≤ opening + 32 * (2 ^ 19 * headers g) at hi
      change packedTraceCount g start w i ≤ cap
      rw [hCap]
      exact hi
  have hBad : physicallyBad = chartBad := by
    funext w
    dsimp only [physicallyBad, chartBad]
    rw [reference_iff_permanent]
    change (¬ Permanent (rawNext s) (fun y i => packedRead s (y i))
      (BStarResetSchedule.run (rawNext s) x w)) = _
    rw [physical_run_eq_fold] <;> rfl
  let deadline := 2 ^ 29 * ClockServiceSpec.longScale n (radWidth s) * headers g
  have hCount : 4 * failureCount physicallyBad deadline ≤
      n ^ deadline + 4 * failureCount missHeader deadline := by
    dsimp only at hSplit
    exact display_count_transport physicallyBad missHeader deadline hSplit
  rw [hBad, hMiss] at hCount
  have hHeaders : headers g = headers j.2 := rfl
  have hNamed : D.deadline ClockServiceSpec.longBudget j =
      2 ^ 29 * ClockServiceSpec.longScale n (radWidth s) * headers j.2 :=
    packed_display_deadline_formula hn hs j ClockServiceSpec.longBudget
  have hDeadline : deadline = D.deadline (2 ^ 32) j :=
    (congrArg (fun m : Nat => 2 ^ 29 * ClockServiceSpec.longScale n (radWidth s) * m)
      hHeaders).trans hNamed.symm
  exact Eq.mp (congrArg (fun t : Nat =>
    4 * failureCount chartBad t ≤ n ^ t + 4 * failureCount missIndex t) hDeadline) hCount

end PackedDisplay

end L4.Height.G9Wire
