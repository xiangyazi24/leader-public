import Leader.L4.ReportReceiptProvenance
import Leader.L4.MonitorRawBridge

namespace L4.ReportLeaseTwoCoverLift
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ReportOwnerResetDrain ReportResetBarrier ShortResetCycle
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem cached_word (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n)) :
    Cached d hh Q (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih =>
    exact ih _ ((cached_fibre d N hh Q F).closed x e X)

private theorem preserve_word (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (P : Raw s n→Prop)
    (step : ∀ x e,Cached d hh Q x→P x→P (rawNext s x e))
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (A : P x) : P (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih =>
    exact ih _ ((cached_fibre d N hh Q F).closed x e X) (step x e X A)

-- CHECK: ReportOwnerReceiptClock.lean:192–200, private run_raw;
-- repeat its proof for the actual cached subtype.
private theorem phase_raw (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (C : Chart h)
    (z : ReportOwnerReceiptClock.State (Cached d hh Q))
    (w : List (Fin n)) :
    (SequentialMarkClock.run
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)) z w).1.val =
      rawRun z.1.val w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change (SequentialMarkClock.run
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e) w).1.val =
      rawRun (rawNext s z.1.val e) w
    rw [ih,ReportOwnerReceiptClock.raw_project]

private theorem advance_raw (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n)) :
    (SequentialMarkClock.run (ReportPrelaunchTwoCovers.advance d hh F N) x w).val =
      rawRun x.val w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    exact ih (ReportPrelaunchTwoCovers.advance d hh F N x e)

/-- A real receipt seeds I at its genuine consume, and its residual
    suffix preserves I, not FullParked. Base can encode global first
    cover ancestry for the second cover. -/
theorem receipt_supplies (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (Base : Raw s n→Prop)
    (baseClosed : ∀ x e,Cached d hh Q x→Base x→Base (rawNext s x e))
    (I : Chart h→Raw s n→Prop)
    (seed : ∀ C y w,Cached d hh Q y→Base y→
      Generated d C y w .done→I C (rawRun y w))
    (closed : ∀ C y e,Cached d hh Q y→I C y→I C (rawNext s y e))
    (C : Chart h) (x : {x : Raw s n // Cached d hh Q x})
    (B : Base x.val) (w : List (Fin n))
    (Hit : ReportOwnerReceiptClock.done (SequentialMarkClock.run
      (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      (x,none) w)) : I C (rawRun x.val w) := by
  -- CHECK: ReportOwnerReceiptClock.lean:242–255.
  obtain ⟨pre,u,post,W,G,_⟩ := ReportOwnerReceiptClock.done_has_genuine_cut
    d C (cached_fibre d N hh Q F) N x w Hit
  have Xpre := cached_word d N hh F x.val x.property pre
  have Bpre := preserve_word d N hh F Base baseClosed x.val x.property pre B
  have A := seed C (rawRun x.val pre) u Xpre Bpre G
  have Xu := cached_word d N hh F (rawRun x.val pre) Xpre u
  have K := preserve_word d N hh F (I C) (closed C)
    (rawRun (rawRun x.val pre) u) Xu post A
  rw [W,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  exact K

/-- All earlier receipts remain valid at the actual end of an Exact
    cover because I is closed. We use the same original physical tape. -/
theorem exact_cover_supplies (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (Base : Raw s n→Prop)
    (baseClosed : ∀ x e,Cached d hh Q x→Base x→Base (rawNext s x e))
    (I : Chart h→Raw s n→Prop)
    (seed : ∀ C y w,Cached d hh Q y→Base y→
      Generated d C y w .done→I C (rawRun y w))
    (closed : ∀ C y e,Cached d hh Q y→I C y→I C (rawNext s y e))
    (sites : List (Chart h)) (x : {x : Raw s n // Cached d hh Q x})
    (B : Base x.val) (w : List (Fin n))
    (R : ReportResetCovers.Exact
      (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
      (fun _=>ReportOwnerReceiptClock.done) none sites (x,none) w) :
    ∀ C∈sites,I C (rawRun x.val w) := by
  induction sites generalizing x w with
  | nil =>
    intro C H
    simp at H
  | cons c cs ih =>
    -- CHECK: ReportResetCovers.lean:14–20, Exact's cons equation.
    obtain ⟨u,v,W,_,_,Hit,Rest⟩ := R
    let z := (SequentialMarkClock.run
      (ReportOwnerReceiptClock.next d c (cached_fibre d N hh Q F))
      (x,none) u).1
    have Z : z.val=rawRun x.val u := phase_raw d N hh F c (x,none) u
    have Bz : Base z.val := by
      rw [Z]
      exact preserve_word d N hh F Base baseClosed x.val x.property u B
    intro C H
    rw [W,ShortOwnerEpochJS.raw_append,←Z]
    rcases List.mem_cons.mp H with E|E
    · subst C
      have A := receipt_supplies d N hh F Base baseClosed I seed closed
        c x B u Hit
      rw [←Z] at A
      exact preserve_word d N hh F (I c) (closed c) z.val z.property v A
    · exact ih z Bz v Rest C E
      -- CHECK: induction-hypothesis argument order depends on elaboration
      -- of B : Base x.val. If needed use named arguments (x:=z) (w:=v).

/-- Two-stage actual cut theorem. Nothing about the residual tail is
    confused with the state at the second cut. The only unproved
    protocol-specific obligations are the explicitly named suppliers. -/
theorem two_covers_supply (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (G : GapInput h)
    (I1 I2 : Chart h→Raw s n→Prop)
    (seed1 : ∀ C y w,Cached d hh Q y→
      Generated d C y w .done→I1 C (rawRun y w))
    (closed1 : ∀ C y e,Cached d hh Q y→I1 C y→I1 C (rawNext s y e))
    (seed2 : ∀ C y w,Cached d hh Q y→
      (∀ D∈ownerCharts G,I1 D y)→
      Generated d C y w .done→I2 C (rawRun y w))
    (closed2 : ∀ C y e,Cached d hh Q y→I2 C y→I2 C (rawNext s y e))
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (Hit : SequentialMarkClock.finished (SequentialMarkClock.run
      (SequentialMarkClock.step (ReportPrelaunchTwoCovers.advance d hh F N)
        (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
        (fun _=>ReportOwnerReceiptClock.done) none)
      (SequentialMarkClock.start none (ownerCharts G++ownerCharts G) x) w)) :
    ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
      (∀ C∈ownerCharts G,I1 C (rawRun x.val u)) ∧
      (∀ C∈ownerCharts G,I1 C (rawRun x.val (u++v)) ∧
        I2 C (rawRun x.val (u++v))) := by
  -- CHECK: ReportPrelaunchTwoCovers.lean:45–64, exact_cuts.
  obtain ⟨u,v,tail,W,U,V⟩ :=
    ReportPrelaunchTwoCovers.exact_cuts d N hh F (ownerCharts G) x w Hit
  let Base : Raw s n→Prop := fun y=>∀ C∈ownerCharts G,I1 C y
  have BC : ∀ y e,Cached d hh Q y→Base y→Base (rawNext s y e) := by
    intro y e Y B C M
    exact closed1 C y e Y (B C M)
  have A : Base (rawRun x.val u) :=
    exact_cover_supplies d N hh F (fun _=>True) (fun _ _ _ _=>trivial)
      I1 (fun C y w Y _ R=>seed1 C y w Y R) closed1
      (ownerCharts G) x trivial u U
  let z := SequentialMarkClock.run (ReportPrelaunchTwoCovers.advance d hh F N) x u
  have Z : z.val=rawRun x.val u := advance_raw d N hh F x u
  have Bz : Base z.val := by rwa [Z]
  have A2 := exact_cover_supplies d N hh F Base BC I2 seed2 closed2
    (ownerCharts G) z Bz v V
  have A1 := preserve_word d N hh F Base BC z.val z.property v Bz
  refine ⟨u,v,tail,W,A,?_⟩
  intro C M
  rw [ShortOwnerEpochJS.raw_append,←Z]
  exact ⟨A1 C M,A2 C M⟩

end L4.ReportLeaseTwoCoverLift

namespace L4.ReportLeaseTwoCoverLift
open AllSizeProtocol PhysicalCustody ReportResetRawHooks ReportOwnerResetDrain
open ReportResetBarrier ShortResetCycle ReportPrelaunchK1Geometry ReportPrelaunchAllOwners
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Terminal soundness for the two-cover clock on the original tape.
The remaining work is entirely in the named seed/closure/target laws. -/
theorem expected_of_two_cover_epochs (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (G : GapInput h)
    (I1 I2 : Chart h→Raw s n→Prop) (Target : Raw s n→Prop)
    (seed1 : ∀ C y w,Cached d hh Q y→
      Generated d C y w .done→I1 C (rawRun y w))
    (closed1 : ∀ C y e,Cached d hh Q y→I1 C y→I1 C (rawNext s y e))
    (seed2 : ∀ C y w,Cached d hh Q y→
      (∀ D∈ownerCharts G,I1 D y)→
      Generated d C y w .done→I2 C (rawRun y w))
    (closed2 : ∀ C y e,Cached d hh Q y→I2 C y→I2 C (rawNext s y e))
    (target : ∀ y,Cached d hh Q y→
      (∀ C∈ownerCharts G,I1 C y ∧ I2 C y)→ Target y)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) Target x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  let advance := ReportPrelaunchTwoCovers.advance d hh F N
  let phase := fun C : Chart h => ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
  let goal := fun (_ : Chart h) (z : ReportOwnerReceiptClock.State (Cached d hh Q)) => ReportOwnerReceiptClock.done z
  let next := SequentialMarkClock.step advance phase goal none
  let start := SequentialMarkClock.start (none : Option Stage) (ownerCharts G++ownerCharts G) x
  have phys : ∀ z e,(next z e).raw.val=rawNext s z.raw.val e := by
    intro z e
    unfold next
    rw [SequentialMarkClock.step_raw _ _ _ _ (fun _ _ _ => rfl)]
    rfl
  apply MonitorRawBridge.expected_of_monitor_words (rawNext s) next
    (fun z => z.raw.val) SequentialMarkClock.finished Target phys start _ _
    (ReportPrelaunchAllOwners.expected d N S hh G Q F x)
  intro w B
  obtain ⟨u,v,tail,E,_,A⟩ :=
    two_covers_supply d N hh F G I1 I2 seed1 closed1 seed2 closed2 x w B
  have Eraw (z : Raw s n) (w : List (Fin n)) :
      SequentialMarkClock.run (rawNext s) z w = rawRun z w := by
    induction w generalizing z with
    | nil => rfl
    | cons e w ih => exact ih (rawNext s z e)
  have Y := cached_word d N hh F x.val x.property (u++v)
  rw [show start.raw.val=x.val from rfl,Eraw,E,ShortOwnerEpochJS.raw_append]
  apply target _ (cached_word d N hh F _ Y tail)
  intro C M
  exact ⟨preserve_word d N hh F (I1 C) (closed1 C) _ Y tail (A C M).1,
    preserve_word d N hh F (I2 C) (closed2 C) _ Y tail (A C M).2⟩

end L4.ReportLeaseTwoCoverLift
