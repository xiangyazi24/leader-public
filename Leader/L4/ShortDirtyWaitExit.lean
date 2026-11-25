import Leader.L4.ShortDirtySweep
import Leader.L4.ShortControllerMIS1

namespace L4.ShortDirtyWaitExit
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetCycle ShortResetForwardH2 ShortDirtySweep ShortControllerMIS1

def AtWait {s n : Nat} (x : Raw s n) (r : Fin n) (op : Nat) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=op

/-- Withholding the door leaves the raw root phase and opcode fixed,
even on its own outgoing row and with arbitrary inherited work. -/
theorem held_source_frame {s n : Nat} (x : Raw s n) (r e : Fin n) (op : Nat)
    (head : header x r=true) (outside : e≠RearTrace.predecessor r)
    (W : AtWait x r op) : AtWait (rawNext s x e) r op := by
  by_cases J : r=e
  · subst e
    have H := reset_controller_outgoing_raw x r head
    exact ⟨H.1.trans W.1,H.2.trans W.2⟩
  have K : r≠rightNeighbor e := by
    intro E
    apply outside
    rw [E,RearTrace.predecessor_right]
  unfold AtWait
  rw [reset_remote_frame_raw x e r J K]
  exact W

theorem held_source_word {s n : Nat} (N : 5≤n) (x : Raw s n) (r : Fin n) (op : Nat)
    (Q : H2Ready x) (head : header x r=true) (W : AtWait x r op)
    (u : List (Fin n)) (out : RearTrace.predecessor r ∉ u) :
    AtWait (rawRun x u) r op := by
  induction u generalizing x with
  | nil => exact W
  | cons e u ih =>
    have release : e≠RearTrace.predecessor r := fun E=>out (E ▸ List.mem_cons_self)
    have no : RearTrace.predecessor r∉u := fun B=>out (List.mem_cons_of_mem _ B)
    have hn : header (rawNext s x e) r=true :=
      (PhysicalCustody.H1.raw_h1_selected_frozen N x e r Q.1).trans head
    exact ih (rawNext s x e) (h2_ready_closed N x e Q) hn
      (held_source_frame x r e op head release W) no

/-- No-forward WAIT on arbitrary inherited bytes admits the exact L+1
selected raw word that exits WAIT, either to ISSUE0 or a lower opcode
debt. This statement is deterministic, not a waiting-time bound. -/
theorem no_forward_wait_exit {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (x : Raw s n) (Q : H2Ready x)
    (heads : ∀ j,header x j=h j) (op : Nat) (valid : op<7)
    (W : AtWait x C.root op) (F : NoForward C x) :
    let w := sweepWord C C.L
    let d := RearTrace.predecessor C.root
    let y := rawNext s (rawRun x w) d
    (w.length+1=C.L+1) ∧ H2Ready y ∧
    (kField 0).read (y C.root).mis1=encode E ∧
    (ShortControllerEntrance.pc (y C.root).mis1=8 ∨ op<6 ∧
      ShortControllerEntrance.pc (y C.root).mis1=8+(op+1) ∧
      6-(ShortControllerEntrance.pc (y C.root).mis1-8)<6-op) := by
  let w := sweepWord C C.L
  let z := rawRun x w
  let d := RearTrace.predecessor C.root
  have R : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  obtain ⟨L,ND,Z,H,NF,P⟩ := packed_of_no_forward C N x Q heads F
  have Hz : header z C.root=true := (H C.root).trans C.rootHeader
  have Wx := held_source_word N x C.root op Q ((heads _).trans C.rootHeader) W w ND
  have K : kind C z 0=(oldK true (z C.root).mis1 0).tag := by
    change (oldK (header z C.root) (z C.root).mis1 (ShortResetChart.lane C.a C.b 0)).tag=_
    rw [Hz,C.rootPort]
  have Qs : (oldK true (z C.root).mis1 0).tag=0 ∨ (oldK true (z C.root).mis1 0).tag=3 := by
    have A := P.1
    rw [K] at A
    exact A
  have noT : (oldK true (z C.root).mis1 0).tag≠1 := by rcases Qs with B|B <;> omega
  have noF : (oldK true (z C.root).mis1 0).tag≠2 := by rcases Qs with B|B <;> omega
  have exit := wait_exit_raw z d (edge_sep (by omega) d) (by rwa [R]) op
    (by simpa only [R] using Wx.1) (by simpa only [R] using Wx.2) valid
    (by simpa only [R] using noT) (by simpa only [R] using noF)
  dsimp only at exit
  rw [R] at exit
  exact ⟨congrArg (fun j=>j+1) L,h2_ready_closed N z d Z,exit⟩

end L4.ShortDirtyWaitExit
