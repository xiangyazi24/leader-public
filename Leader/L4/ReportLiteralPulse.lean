import Leader.L4.ReportPulseRaw
import Leader.L4.ReportPulseGateGeometry
import Leader.L4.ReportStickyRawCover

namespace L4.ReportLiteralPulse
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportPrelaunchK1Geometry ReportLeaseOwner
open ReportByteRows ReportPulseRaw ReportPulseGateGeometry ReportStickyRawCover
open ReportProtectedInterval ReportStaticSpacing

variable {s n : Nat} {h : Fin n→Bool}

private theorem outgoing_never_paints (p : Params) (x : BitVec p.w) :
    paints p true 2 x=false := by
  unfold paints
  dsimp only
  generalize (if ((x.extractLsb' (ell p.streak) 2).toNat==3) then 0
      else (x.extractLsb' (ell p.streak) 2).toNat)=r
  split <;> (first | rfl | split <;> simp_all)

/-- The old endpoint branch is the same projection used by the
two-label counted clock, on either literal report sheet. -/
theorem rawPaint_eq_countedPaint (d : Sheet) (N : 1<n)
    (x : Raw s n) (e : Fin n) (i : Owner h) :
    rawPaint d h x e i =
      countedPaint i.val (params d s) (fun y=>selectBytes d (y i.val)) x e := by
  unfold rawPaint countedPaint
  by_cases L : i.val=e
  · have H : i.val≠rightNeighbor e := by rw [L]; exact edge_sep N e
    rw [if_pos L,if_neg H,outgoing_never_paints]
  · rw [if_neg L]

theorem countedPaint_incoming (d : Sheet) (x : Raw s n) (e : Fin n) (i : Owner h)
    (A : countedPaint i.val (params d s) (fun y=>selectBytes d (y i.val)) x e=true) :
    e=put (i,false) := by
  unfold countedPaint at A
  split at A
  · rename_i E
    change e=RearTrace.predecessor i.val
    rw [E,RearTrace.predecessor_right]
  · contradiction

/-- Distinct gates cannot complete a pulse on a single physical mark.
The conclusion does not assume either mark changes the visible Z bit. -/
theorem distinct_gates_cannot_paint (d : Sheet) (N : 1<n)
    (G : GapInput h) (x : Raw s n) (e : Fin n) (i j : Owner h)
    (D : i≠j) (A : rawPaint d h x e i=true) :
    rawPaint d h x e j=false := by
  apply Bool.eq_false_iff.mpr
  intro B
  rw [rawPaint_eq_countedPaint d N] at A B
  have E := (countedPaint_incoming d x e i A).symm.trans (countedPaint_incoming d x e j B)
  exact D (congrArg Prod.fst (put_injective G E))

/-- Direct deterministic observations for ReportTrialToSticky:
a counted paint adopts the old B-zero decision, and an uncounted
mark frames Z. Old selected B is used even on a simultaneous COMMIT. -/
theorem counted_observation (d : Sheet) (N : 1<n) (x : Raw s n) (e : Fin n) (i : Owner h)
    (Mask : ∀ k, lower d (oldHeaders (rows s) (x k))=h k) :
    let P := countedPaint i.val (params d s) (fun y=>selectBytes d (y i.val)) x e
    let R := readout d h
    (P=true → R.z (rawNext s x e) i=(R.b x i==0)) ∧
      (P=false → R.z (rawNext s x e) i=R.z x i) := by
  let P := countedPaint i.val (params d s) (fun y=>selectBytes d (y i.val)) x e
  have E := raw_pulse d h x e i (edge_sep N e) Mask
  rw [rawPaint_eq_countedPaint d N] at E
  change (readout d h).z (rawNext s x e) i =
    (if P then (readout d h).b x i==0 else (readout d h).z x i) at E
  constructor
  · intro A
    change P=_ at A
    rw [A] at E
    exact E
  · intro A
    change P=_ at A
    rw [A] at E
    exact E

#print axioms rawPaint_eq_countedPaint
#print axioms countedPaint_incoming
#print axioms distinct_gates_cannot_paint
#print axioms counted_observation
end L4.ReportLiteralPulse
