import Leader.L4.ReportOwnerSerial
import Leader.L4.ReportLeaseGrants

namespace L4.ReportFirstCutGrant
open AllSizeProtocol PhysicalCustody Height ReportOwnerSerial ReportResetRawHooks ShortResetCycle
open ReportResetBarrier ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseGrants ReportJoinedGrants BStarShort ReportPrelaunchAllOwners

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem raw_compatible_on_touch (d : Sheet) (x : Raw s n) (e i : Fin n)
    (N : e≠rightNeighbor e) (Touch : i=e ∨ i=rightNeighbor e) :
    Compatible (rawGrant d (rawNext s x e) i) := by
  rcases Touch with L|R
  · subst i
    have E : rawGrant d (rawNext s x e) e =
        (oldView (params d s) (lower d (oldHeaders (rows s) (x e)))
          (selectBytes d (x e))).nextValue :=
      funext fun j => (raw_grant_rows d x e N j).1
    rw [E]
    exact next_compatible _
  · subst i
    let hv := lower d (oldHeaders (rows s) (x (rightNeighbor e)))
    let g := oldView (params d s) hv (selectBytes d (x (rightNeighbor e)))
    have E : rawGrant d (rawNext s x e) (rightNeighbor e) =
        (if hv then g.canonical else fun _ => false) := by
      funext j
      have D := (raw_grant_rows d x e N j).2
      change _ = if hv then g.canonical j else false at D
      split <;> rename_i K <;> simpa [K] using D
    rw [E]
    split
    · exact canonical_compatible _
    · intro H; contradiction

theorem generated_root_compatible (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (w : List (Fin n)) (k : Stage) (R : Generated d C x w k) :
    Compatible (rawGrant d (rawRun x w) C.root) := by
  induction R with
  | issue P =>
    change Compatible (rawGrant d (rawNext s x (door C)) C.root)
    apply raw_compatible_on_touch d x (door C) C.root (edge_sep N _)
    exact .inr (RearTrace.right_predecessor C.root).symm
  | snoc e R K IH =>
    rw [ShortOwnerEpochJS.raw_append]
    change Compatible (rawGrant d (rawNext s (rawRun x _) e) C.root)
    exact raw_compatible_step d _ e C.root (edge_sep N e) IH

def AllHeaderCompatible (d : Sheet) (h : Fin n→Bool) (x : Raw s n) : Prop :=
  ∀ i,h i=true→Compatible (rawGrant d x i)

theorem headers_compatible_at_first_cut (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (E : ReportReceiptProvenance.ExactCover d N hh F (ownerCharts G) x w) :
    AllHeaderCompatible d h (rawRun x.val w) := by
  intro i I
  obtain ⟨C,M,R⟩ := owner_charts_cover G i I
  have H := ReportLeaseTwoCoverLift.exact_cover_supplies d N hh F
    (fun _=>True) (fun _ _ _ _=>trivial)
    (fun C (y : Raw s n) => Compatible (rawGrant d y C.root))
    (fun C y u _ _ P => generated_root_compatible d C N y u .done P)
    (fun C y e _ T => raw_compatible_step d y e C.root (edge_sep N e) T)
    (ownerCharts G) x trivial w E C M
  simpa only [R] using H

def AllSerialCompatible (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop)
    (G : GapInput h) (x : Raw s n) : Prop :=
  AllSerial d hh Q G x ∧ AllHeaderCompatible d h x

theorem all_serial_compatible_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (e : Fin n)
    (A : AllSerialCompatible d hh Q G x) : AllSerialCompatible d hh Q G (rawNext s x e) := by
  exact ⟨all_serial_closed d N hh G F digit x e A.1,
    fun i I => raw_compatible_step d x e i (edge_sep N e) (A.2 i I)⟩

theorem all_serial_compatible_from_cached (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (AllSerialCompatible d hh Q G) x.val
      (ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  let advance := ReportPrelaunchTwoCovers.advance d hh F N
  let phase := fun C : Chart h => ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
  let goal := fun (_ : Chart h) (z : ReportOwnerReceiptClock.State (Cached d hh Q)) =>
    ReportOwnerReceiptClock.done z
  let fresh : Option Stage := none
  let sites := ReportPrelaunchAllOwners.ownerCharts G
  let next := SequentialMarkClock.step advance phase goal fresh
  let start := SequentialMarkClock.start fresh sites x
  let K := ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits
  have digit := ReportPrelaunchDoorProducer.digits_positive d S
  have phys : ∀ C w e,(phase C w e).1=advance w.1 e := fun _ _ _ => rfl
  have project : ∀ z e,(next z e).raw.val=rawNext s z.raw.val e := by
    intro z e
    unfold next
    rw [SequentialMarkClock.step_raw _ _ _ _ phys]
    rfl
  have initial (C : Chart h) (y : {x : Raw s n // Cached d hh Q x}) :
      ¬goal C (y,fresh) := ReportOwnerReceiptClock.initial_not_done y
  have bound := SequentialMarkClock.expected advance phase goal fresh (fun _=>True) phys
    (fun _ _ _=>trivial) (n*K) (fun C y _=>initial C y)
    (fun C y _=>ReportPrelaunchDoorReady.receipt_mean d C N S hh G Q F y)
    sites x trivial
  have H := MonitorRawBridge.expected_of_monitor_words (rawNext s) next
    (fun z => z.raw.val) SequentialMarkClock.finished (AllSerialCompatible d hh Q G)
    project start (by
      intro word done
      have before : SequentialMarkClock.BeforeCurrent goal start := by
        unfold SequentialMarkClock.BeforeCurrent start SequentialMarkClock.start
        cases sites with
        | nil => trivial
        | cons C _ => exact initial C x
      have W := SequentialMarkClock.first_hit_receipts_of_finished advance phase goal fresh
        initial start word before done
      have R : SequentialMarkClock.FirstHitReceipts phase goal fresh (sites++[]) (x,fresh) word := by
        rw [List.append_nil]
        exact W
      obtain ⟨u,v,E,U,_⟩ := ReportResetCovers.split_first_cut advance phase goal fresh phys sites [] x word R
      have A : AllSerialCompatible d hh Q G (rawRun x.val u) := by
        refine ⟨?_,headers_compatible_at_first_cut d N hh G F x u U⟩
        have lift (y : Raw s n) (w : List (Fin n)) (Y : Cached d hh Q y) :
            Cached d hh Q (rawRun y w) := by
          induction w generalizing y with
          | nil => exact Y
          | cons e w ih => exact ih _ ((cached_fibre d N hh Q F).closed y e Y)
        refine ⟨lift _ u x.property,?_⟩
        apply ReportLeaseTwoCoverLift.exact_cover_supplies d N hh F (fun _ => True)
          (fun _ _ _ _ => trivial) (Serial d) _ _ sites x trivial u U
        · exact fun C y w Y _ P=>seed_at_genuine_receipt d C N hh F y Y w P
        · exact fun C y e Y T=>all_mark d C N hh G F y Y T digit e
      have runs (y : Raw s n) (w : List (Fin n)) :
          SequentialMarkClock.run (rawNext s) y w=rawRun y w := by
        induction w generalizing y with
        | nil => rfl
        | cons e w ih => exact ih (rawNext s y e)
      have stepper (y : Raw s n) (w : List (Fin n)) (a : AllSerialCompatible d hh Q G y) :
          AllSerialCompatible d hh Q G (rawRun y w) := by
        induction w generalizing y with
        | nil => exact a
        | cons e w ih => exact ih _ (all_serial_compatible_closed d N hh G F digit y e a)
      rw [show start.raw.val=x.val from rfl,runs,E,ShortOwnerEpochJS.raw_append]
      exact stepper _ v A) _ bound
  have len : sites.length≤n := ReportPrelaunchAllOwners.owner_charts_length G
  have up : sites.length*(n*K)≤K*n^2 := by
    calc
      _ ≤ n*(n*K) := Nat.mul_le_mul_right _ len
      _ = _ := by rw [Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ up)

#print axioms all_serial_compatible_closed
#print axioms all_serial_compatible_from_cached
#print axioms raw_compatible_on_touch
#print axioms generated_root_compatible
#print axioms headers_compatible_at_first_cut
end L4.ReportFirstCutGrant
