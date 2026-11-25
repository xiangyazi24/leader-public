import Leader.L4.ReportFastMappedFence
import Leader.L4.ReportFastAcqWins

namespace L4.ReportFastAcqMapped
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportFastOwnerSupport ReportOwnerAcquireProvenance
open ReportFastNominationBridge ReportFastDenySteering
open ReportFastFiveGeometry ReportFastPrepMapping ReportFastMappedFence
open ReportFastAcqWins

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem fenced_of_prefixes (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (H : BeforeConsume d C x w)
    (R : ∀ u v, w=u++v → RivalFence d C (rawRun x u)) :
    FencedBefore d C x w := by
  induction H with
  | nil => exact .nil
  | @snoc u e T NC IH =>
    refine .snoc e (IH (fun a v V=>R a (v++[e]) (by rw [V,List.append_assoc]))) NC ?_
    intro _ _ _ _ _
    exact R u [e] rfl

/-- Every stopped prefix in the ACQ portion of the original mapped word
inherits the genuine rival receipts from the preparation prefix.
The profile is allowed to switch the target after preparation. -/
theorem mapped_acq_fenced_before
    (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Fin 5→Owner h) (R : Consecutive G r)
    (incl : ∀ j,∃ i,C i=charter G (r j))
    (x : {y : Raw s n // Cached d hh Q y}) (prep preacq draws : List (Fin n))
    (t : Nat) (P : Nat → Raw s n → Fin 5 → Bool)
    (prior : ∀ a y,t≤a → a<t+prep.length → P a y=denySides)
    (deny : ∀ a y j,j≠2 → P a y j=false)
    (done : (SequentialMarkClock.run
      (fun z e=>ReportFastSixPrep.step d C N hh F z
        (ReportAdaptiveFibre.mergeSide
          (ReportFastSixPrepTrack.prepBan d (fun j=>charter G (r j)) z) e))
      (ReportFastSixPrep.init d hh x) prep).2=none) :
    let B := fun j=>charter G (r j)
    let a := rawRun x.val (mappedWord d B P t x.val (prep++preacq))
    let w := mappedWord d B P (t+(prep++preacq).length) a draws
    BeforeConsume d (B 2) a w → FencedBefore d (B 2) a w := by
  let B := fun j=>charter G (r j)
  let initMarks := mappedWord d B P t x.val (prep++preacq)
  let a := rawRun x.val initMarks
  let t' := t+(prep++preacq).length
  let w := mappedWord d B P t' a draws
  change BeforeConsume d (B 2) a w → FencedBefore d (B 2) a w
  intro BC
  apply fenced_of_prefixes d (B 2) a w BC
  intro u v E
  let ud := draws.take u.length
  let vd := draws.drop u.length
  have len : u.length≤draws.length := by
    have L := mappedWord_length d B P t' a draws
    change w.length=_ at L
    rw [E,List.length_append] at L
    omega
  have M := mappedWord_append d B P t' a ud vd
  rw [show ud++vd=draws from List.take_append_drop _ _,show mappedWord d B P t' a draws=w from rfl,E] at M
  have Eq : u=mappedWord d B P t' a ud :=
    List.append_inj_left M (by rw [mappedWord_length]; simp [ud,Nat.min_eq_left len])
  have I := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  have Hist := prepared_mapped_receiptSuffix d C B N hh G F I incl x prep
    (preacq++ud) t P prior done
  have S : mappedWord d B P t x.val (prep++(preacq++ud))=initMarks++u := by
    rw [←List.append_assoc,mappedWord_append,Eq]
  have RC := target_rival_fence_of_receipts d N hh G F digit r R P deny
    x.val x.property _ (fun j J=>Hist j)
  change RivalFence d (B 2) (rawRun a u)
  rw [show rawRun a u=rawRun x.val (mappedWord d B P t x.val (prep++(preacq++ud))) by
    rw [S,ShortOwnerEpochJS.raw_append]]
  exact RC

#print axioms fenced_of_prefixes
#print axioms mapped_acq_fenced_before

end L4.ReportFastAcqMapped
