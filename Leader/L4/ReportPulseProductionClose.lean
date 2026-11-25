import Leader.L4.ReportPulseJointLoss
import Leader.L4.ReportPulseGateGeometry
import Leader.L4.ReportServiceMesh

namespace L4.ReportPulseProductionClose
open AdviceBandRadiusBudget ReportLossArithmetic FourLossStickyClock
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetRawHooks
open ReportByteRows ReportPulseRaw ReportPulseWarmup ReportPulseRecode
open ReportPulseWinsSkeleton ReportPulseJointLoss ReportServiceMesh
open ReportPrelaunchK1Geometry ReportLeaseOwner ReportOwnerResetDrain

variable {s n m : Nat} {h : Fin n→Bool}

def gateBytes (d : Sheet) (a : Owner h) (x : Raw s n) : BitVec (params d s).w :=
  selectBytes d (x a.val)

def sheetCloseLoss (d : Sheet) (gate : Fin m→Owner h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  closeLoss (meshRadius d s) gate (rawNext s) ReportPulseGateGeometry.put
    (params d s) (gateBytes d) x w

def initialPhase (d : Sheet) (x : Raw s n) : Phase (Owner h) :=
  fun g=>phaseOf (readClock (params d s) (gateBytes d g) x).phase

theorem sheet_streak (d : Sheet) (s : Nat) :
    (params d s).streak=trialJ (meshRadius d s) := by
  cases d <;> rfl

theorem trial_budget (rho : Nat) (N : 0<n) :
    2≤n*trialU rho ∧ 2*trialJ rho≤n*trialU rho := by
  have J : 0<trialJ rho := by rw [trialJ_eq_streak]; exact streak_pos rho
  have M : 2≤4096*trialH rho := by unfold trialH; omega
  have K : 2*trialJ rho≤n*trialU rho :=
    calc
      _ ≤ (4096*trialH rho)*trialJ rho := Nat.mul_le_mul_right _ M
      _ ≤ trialU rho := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
      _ ≤ n*trialU rho := Nat.le_mul_of_pos_left _ N
  exact ⟨Nat.le_trans (by omega) K,K⟩

theorem literal_sheet_wire (d : Sheet) (Q : Raw s n→Prop)
    (stay : ∀ x e,Q x→Q (rawNext s x e))
    (b : Owner h)
    (freeze : ∀ x,Q x→lower d (oldHeaders (rows s) (x b.val))=true) :
    Wire (rawNext s) (ReportPulseGateGeometry.put (b,true)) Q (params d s) (gateBytes d b) := by
  cases d
  · exact wire1 b.val Q stay freeze
  · exact wire2 b.val Q stay freeze

theorem sheet_close_loss_count (d : Sheet) (N : 0<n)
    (G : GapInput h) (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q)
    (gate : Fin m→Owner h) (Many : m≤9*trialH (meshRadius d s))
    (x : Raw s n) (Good : Q x) :
    let B := n*trialU (meshRadius d s)
    8*badCount (sheetCloseLoss d gate x) B≤n^B := by
  dsimp only
  let rho := meshRadius d s
  have S := sheet_streak d s
  have J : 0<(params d s).streak := by rw [S,trialJ_eq_streak]; exact streak_pos rho
  have W := trial_budget (n:=n) rho N
  have K : 2*(params d s).streak≤n*trialU rho := by rw [S]; exact W.2
  exact actual_close_loss rho gate (rawNext s) ReportPulseGateGeometry.put
    (ReportPulseGateGeometry.put_injective G) (params d s) (gateBytes d) Q
    (fun b => literal_sheet_wire d Q F.closed b
      (fun y Y => (F.mask y Y b.val).trans b.property))
    (fun b => RearTrace.right_predecessor b.val)
    x Good (initialPhase d x) (fun _=>rfl) S J N Many W.1 K

end L4.ReportPulseProductionClose
