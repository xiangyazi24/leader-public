import Leader.L4.ReportFastGateRaw
import Leader.L4.ReportFastOwnerSupport
namespace L4.ReportFastNoRearm
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportPrelaunchClock ReportByteRows
open ReportGoodEightBank ReportGoodEightCut ReportPrelaunchAllOwners
open ReportFastGateRaw ReportFastOwnerSupport

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem fast_norm_fixed (p : Params) (w : BitVec (tokenW p))
    (side : Nat) (H : healthyAdmit p (decode p true w))
    (R1 : (decode p true w).race≠1)
    (R2 : (decode p true w).race≠(if side=3 then 2 else 3)) :
    rankNormWire p side true w=w := by
  simp [rankNormWire,rankNormIntent,H.1,H.2.1,H.2.2,R1,R2]

private theorem front_tag_iff (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_not_front (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem actual_front (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i<C.L)
    (T : (tok d C x i).tag=2) : ForwardWait d C x i := by
  rcases S with A|⟨k,A⟩|⟨k,A⟩
  · have B := A.2.2 i I
    omega
  · have E := (front_tag_iff k i).mp ((A.2.2 i I).symm.trans T)
    exact E ▸ A
  · exact False.elim (back_not_front k i ((A.2.2 i I).symm.trans T))

private theorem gate_predecessor_trail (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i+1<C.L)
    (H : healthyAdmit (params d s) (tok d C x (i+1))) :
    (tok d C x i).tag=1 := by
  have A := actual_front d C x S (i+1) I H.1
  simpa [frontTag,show i<i+1 by omega] using A.2.2 i (by omega)

-- Spectator marks are exact wire frames.  The other endpoint
-- cannot be the gate if neither incidence is marked.
theorem raw_gate_spectator (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (I : i+1<C.L)
    (e : Fin n) (A : e≠out C i) (B : e≠out C (i+1)) :
    tok d C (rawNext s x e) (i+1)=tok d C x (i+1) := by
  have Y := (cached_fibre d N hh Q F).closed x e X
  apply decoded_frame d C hh G x _ X Y (i+1) I
  unfold wire
  have R : out C (i+1)≠rightNeighbor e := by
    intro E
    have K : rightNeighbor (out C i)=rightNeighbor e :=
      (chart_succ C i).trans E
    exact A ((ShortChartOwnership.right_injective K).symm)
  rw [ReportRawProjection.raw_spectator x e _ (Ne.symm B) R]

-- Fixed-side no-rearm: settled incoming race 2 cannot change
-- without the outgoing mark, settled outgoing race 3 without incoming.
theorem raw_no_rearm_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (S : Serial d C x)
    (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x (i+1)=true)
    (H : healthyAdmit (params d s) (tok d C x (i+1)))
    (side : Bool) (R : (tok d C x (i+1)).race=(if side then 3 else 2))
    (e : Fin n) (E : e≠(if side then out C i else out C (i+1))) :
    tok d C (rawNext s x e) (i+1)=tok d C x (i+1) := by
  let p := params d s
  have T : tok d C x (i+1)=decode p true (wire d C x (i+1)) := by rw [tok_wire,A]
  have H' := H
  rw [T] at H'
  cases side
  · change e≠out C (i+1) at E
    change (tok d C x (i+1)).race=2 at R
    by_cases D : e=out C i
    · subst e
      have P : (tok d C x i).tag≠2 := by
        rw [gate_predecessor_trail d C x S i I H]; decide
      rw [raw_in_norm d C N hh G F x X i I A P H]
      have B : (decode p true (wire d C x (i+1))).race=2 := by rwa [T] at R
      rw [fast_norm_fixed p _ 2 H' (by omega) (by simp [B])]
      exact T.symm
    · exact raw_gate_spectator d C N hh G F x X i I e D E
  · change e≠out C i at E
    change (tok d C x (i+1)).race=3 at R
    by_cases D : e=out C (i+1)
    · subst e
      rw [raw_out_norm d C N hh G F x X (i+1) I A H (by omega)]
      have B : (decode p true (wire d C x (i+1))).race=3 := by rwa [T] at R
      rw [fast_norm_fixed p _ 3 H' (by omega) (by simp [B])]
      exact T.symm
    · exact raw_gate_spectator d C N hh G F x X i I e E D

-- The whole intervening original tape, not a resampled process.
theorem raw_no_rearm_word (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (i : Nat) (I : i+1<C.L) (A : chartGate d C x (i+1)=true)
    (H : healthyAdmit (params d s) (tok d C x (i+1)))
    (side : Bool) (R : (tok d C x (i+1)).race=(if side then 3 else 2))
    (w : List (Fin n))
    (E : ∀ e∈w,e≠(if side then out C i else out C (i+1))) :
    tok d C (rawRun x w) (i+1)=tok d C x (i+1) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w IH =>
    let y := rawNext s x e
    have Y := (cached_fibre d N hh Q F).closed x e X
    have S' := strong_step d C N hh G F x X S digit e
    have A' : chartGate d C y (i+1)=true :=
      (gate_frame d C hh G x y X Y (i+1) I).trans A
    have W := raw_no_rearm_step d C N hh G F x X S.1 i I A H side R e
      (E e (by simp))
    have H' : healthyAdmit (params d s) (tok d C y (i+1)) := by rw [W]; exact H
    have R' : (tok d C y (i+1)).race=(if side then 3 else 2) := by rw [W]; exact R
    exact (IH y Y S' A' H' R' (fun a M=>E a (by simp [M]))).trans W

#print axioms raw_gate_spectator
#print axioms raw_no_rearm_step
#print axioms raw_no_rearm_word
end L4.ReportFastNoRearm
