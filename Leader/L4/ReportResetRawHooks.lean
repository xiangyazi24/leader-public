import Leader.L4.ReportResetBarrier
import Leader.L4.ReportRawProjection

namespace L4.ReportResetRawHooks
open AllSizeProtocol PhysicalCustody ReportByteRows ReportRawProjection
open ShortResetCycle ShortResetChart ShortResetRow
open ReportResetBarrier

inductive Sheet where
  | first | second

def params (d : Sheet) (s : Nat) : Params :=
  match d with
  | .first => firstParams s
  | .second => secondParams s

def selectBytes (d : Sheet) {s : Nat} (x : LargeSite (Prod s)) : BitVec (params d s).w :=
  match d with
  | .first => x.report1
  | .second => x.report2

def lower (d : Sheet) (b : Headers) : Bool :=
  match d with
  | .first => b.h4
  | .second => b.h5

def wire (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (k : Nat) : BitVec (tokenW (params d s)) :=
  resetTokenRead (params d s) (selectBytes d (x (out C k))) (C.route.port k)

theorem raw_token_control (d : Sheet) {s n : Nat} (x : Raw s n) (e : Fin n)
    (N : e≠rightNeighbor e) :
    let p := params d s
    let v := rightNeighbor e
    let h := (lower d (oldHeaders (rows s) (x e)),lower d (oldHeaders (rows s) (x v)))
    let xpair := (selectBytes d (x e),selectBytes d (x v))
    Pair.map (tokenControl p) (selectBytes d (rawNext s x e e),selectBytes d (rawNext s x e v)) =
      Pair.map (tokenControl p) (patchPair (row p h xpair) xpair) := by
  cases d with
  | first => exact raw_report1_token_control x e N
  | second => exact raw_report2_token_control x e N

theorem dest_eq (h : Bool) (j : Fin 3) :
    reset0Destination h j=ShortResetRow.destination h j := by
  cases h
  · rfl
  · have Q : j=0 ∨ j=1 ∨ j=2 := by
      have B := j.isLt
      rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with H|H|H
      · exact .inl (Fin.ext H)
      · exact .inr (.inl (Fin.ext H))
      · exact .inr (.inr (Fin.ext H))
    rcases Q with rfl|rfl|rfl <;> decide

theorem raw_off_frame (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (D : e≠door C) (Q : ∀ j, j<C.L → e≠out C j)
    (k : Nat) (K : k<C.L) :
    wire d C (rawNext s x e) k=wire d C x k := by
  have R : out C k≠rightNeighbor e := by
    intro T
    cases k with
    | zero =>
      have E : e=door C := by
        have H := congrArg RearTrace.predecessor T
        change e=RearTrace.predecessor (out C 0)
        simpa only [RearTrace.predecessor_right] using H.symm
      exact D E
    | succ k =>
      have E : e=out C k := ShortChartOwnership.right_injective T.symm
      exact Q k (by omega) E
  unfold wire
  rw [raw_spectator x e _ (Ne.symm (Q k K)) R]

theorem raw_door_frame (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (k : Nat) (P : 0<k) (K : k<C.L) :
    wire d C (rawNext s x (door C)) k=wire d C x k := by
  have L := C.length_lt
  have R : out C k≠rightNeighbor (door C) := by
    intro H
    have E : nextAt C.root k=nextAt C.root 0 := H.trans (RearTrace.right_predecessor C.root)
    have Z := nextAt_injective_under C.root _ _ (by omega) (by omega) E
    omega
  unfold wire
  rw [raw_spectator x (door C) _ (Ne.symm (ReportChartPartition.door_not_outgoing C k K)) R]

theorem raw_link_frame (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (j k : Nat) (J : j<C.L) (K : k<C.L) (A : k≠j) (B : k≠j+1) :
    wire d C (rawNext s x (out C j)) k=wire d C x k := by
  have L := C.length_lt
  have E : out C k≠out C j :=
    fun Q=>A (nextAt_injective_under C.root _ _ (by omega) (by omega) Q)
  have R : out C k≠rightNeighbor (out C j) :=
    fun Q=>B (nextAt_injective_under C.root _ _ (by omega) (by omega) Q)
  unfold wire
  rw [raw_spectator x (out C j) _ E R]

/-- An actual sampled report hop under only the old frozen header mask.
There is deliberately no hypothesis of an empty next occurrence. -/
theorem raw_forward_hop (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (J : j+1<C.L)
    (sep : out C j≠rightNeighbor (out C j))
    (F : publicationToken (params d s) (h (out C j)) (selectBytes d (x (out C j)))
      (C.route.port j)=reset0Forward) :
    wire d C (rawNext s x (out C j)) j=resetTokenWire (params d s) MISByteCodec.T ∧
    wire d C (rawNext s x (out C j)) (j+1)=resetTokenWire (params d s) reset0Forward := by
  let e := out C j
  let r := rightNeighbor e
  have L := C.route.live j J
  change destination (h r) (C.route.port j)=some (C.route.port (j+1)) at L
  have P := raw_token_control d x e sep
  dsimp only at P
  rw [mask e,mask r] at P
  have W := reset0_row_hop (params d s) (h e) (h r) (selectBytes d (x e))
    (selectBytes d (x r)) (C.route.port j) (C.route.port (j+1)) F
    ((dest_eq _ _).trans L)
  exact ⟨(congrArg (fun z=>(z.1.1) (C.route.port j)) P).trans W.1,
    (congrArg (fun z=>(z.2.1) (C.route.port (j+1))) P).trans W.2⟩

theorem raw_forward_turn (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (J : j+1=C.L)
    (sep : out C j≠rightNeighbor (out C j))
    (F : publicationToken (params d s) (h (out C j)) (selectBytes d (x (out C j)))
      (C.route.port j)=reset0Forward) :
    wire d C (rawNext s x (out C j)) j=resetTokenWire (params d s) reset0Reply := by
  let e := out C j
  let r := rightNeighbor e
  have L := C.route.turn
  have E : C.L-1=j := by omega
  change destination (h (rightNeighbor (out C (C.L-1)))) (C.route.port (C.L-1))=none at L
  rw [E] at L
  change destination (h r) (C.route.port j)=none at L
  have P := raw_token_control d x e sep
  dsimp only at P
  rw [mask e,mask r] at P
  have W := reset0_row_turn (params d s) (h e) (h r) (selectBytes d (x e))
    (selectBytes d (x r)) (C.route.port j) F ((dest_eq _ _).trans L)
  exact (congrArg (fun z=>(z.1.1) (C.route.port j)) P).trans W

/-- The actual report reverse mark preserves the reset reply and
clears its old successor wire after all other joined work. -/
theorem raw_backward (d : Sheet) {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (j : Nat) (J : j+1<C.L)
    (sep : out C j≠rightNeighbor (out C j))
    (F : (publicationToken (params d s) (h (out C j)) (selectBytes d (x (out C j)))
      (C.route.port j)).tag≠2)
    (D : publicationToken (params d s) (h (out C (j+1))) (selectBytes d (x (out C (j+1))))
      (C.route.port (j+1))=reset0Reply) :
    wire d C (rawNext s x (out C j)) j=resetTokenWire (params d s) reset0Reply ∧
    wire d C (rawNext s x (out C j)) (j+1)=resetTokenWire (params d s) MISByteCodec.E := by
  let e := out C j
  let r := rightNeighbor e
  have L := C.route.live j J
  change destination (h r) (C.route.port j)=some (C.route.port (j+1)) at L
  have P := raw_token_control d x e sep
  dsimp only at P
  rw [mask e,mask r] at P
  have W := reset0_row_reverse (params d s) (h e) (h r) (selectBytes d (x e))
    (selectBytes d (x r)) (C.route.port j) (C.route.port (j+1)) F D
    ((dest_eq _ _).trans L)
  exact ⟨(congrArg (fun z=>(z.1.1) (C.route.port j)) P).trans W.1,
    (congrArg (fun z=>(z.2.1) (C.route.port (j+1))) P).trans W.2⟩

theorem read_forward0 (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3)
    (H : resetTokenRead p x j=resetTokenWire p reset0Forward) :
    publicationToken p h x j=reset0Forward := by
  change decode p _ (resetTokenRead p x j)=reset0Forward
  rw [H]
  exact reset0_decode_forward _ _

theorem read_reply0 (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3)
    (H : resetTokenRead p x j=resetTokenWire p reset0Reply) :
    publicationToken p h x j=reset0Reply := by
  change decode p _ (resetTokenRead p x j)=reset0Reply
  rw [H]
  exact reset0_decode_reply _ _

#print axioms raw_token_control
#print axioms dest_eq
#print axioms raw_off_frame
#print axioms raw_door_frame
#print axioms raw_link_frame
#print axioms raw_forward_hop
#print axioms raw_forward_turn
#print axioms raw_backward
#print axioms read_forward0
#print axioms read_reply0
end L4.ReportResetRawHooks
