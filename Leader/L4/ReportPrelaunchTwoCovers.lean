import Leader.L4.ReportPrelaunchDoorReady
import Leader.L4.ReportResetCovers

namespace L4.ReportPrelaunchTwoCovers
open PhysicalCustody ReportResetRawHooks ReportResetBarrier ShortResetCycle
open ReportOwnerResetDrain ReportPrelaunchK1Geometry

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n→Prop}

def advance (d : Sheet) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : {x : Raw s n // Cached d hh Q x}) (e : Fin n) :
    {x : Raw s n // Cached d hh Q x} :=
  ⟨rawNext s x.val e,(cached_fibre d N hh Q F).closed _ _ x.property⟩

/-- Two chronological cover lists run on one raw tape. This clock
    charges genuine first receipts, not a terminal custody assertion. -/
theorem monitor_expected (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (sites : List (Chart h)) (L : sites.length≤n)
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost
      (SequentialMarkClock.step (advance d hh F N)
        (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
        (fun _=>ReportOwnerReceiptClock.done) none)
      SequentialMarkClock.finished (SequentialMarkClock.start none (sites++sites) x)
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  let K := ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits
  let phase := fun C : Chart h=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
  have R := SequentialMarkClock.expected (advance d hh F N) phase
    (fun _=>ReportOwnerReceiptClock.done) none (fun _=>True)
    (fun _ _ _=>rfl) (fun _ _ _=>trivial) (n*K)
    (fun _ y _=>ReportOwnerReceiptClock.initial_not_done y)
    (fun C y _=>ReportPrelaunchDoorReady.receipt_mean d C N S hh G Q F y)
    (sites++sites) x trivial
  have B : (sites++sites).length*(n*K)≤2*K*n^2 := by
    rw [List.length_append]
    calc
      _ ≤ (n+n)*(n*K) := Nat.mul_le_mul_right _ (Nat.add_le_add L L)
      _ = _ := by rw [←Nat.two_mul,Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (R t) (Nat.mul_le_mul_right _ B)

/-- A finished observer splits its one mark tape into the two actual
    first-receipt cover cuts. No new scheduler is sampled at the split. -/
theorem exact_cuts (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (sites : List (Chart h)) (x : {x : Raw s n // Cached d hh Q x})
    (w : List (Fin n)) :
    let phase := fun C : Chart h=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
    let goal := fun _ : Chart h=>ReportOwnerReceiptClock.done
    let A := advance d hh F N
    SequentialMarkClock.finished (SequentialMarkClock.run
      (SequentialMarkClock.step A phase goal none)
      (SequentialMarkClock.start none (sites++sites) x) w) →
      ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
        ReportResetCovers.Exact phase goal none sites (x,none) u ∧
        ReportResetCovers.Exact phase goal none sites (SequentialMarkClock.run A x u,none) v := by
  dsimp only
  apply ReportResetCovers.two_covers_cuts
  · intro _ _ _
    rfl
  · intro _ y
    exact ReportOwnerReceiptClock.initial_not_done y

#print axioms monitor_expected
#print axioms exact_cuts
end L4.ReportPrelaunchTwoCovers
