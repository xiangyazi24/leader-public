import Leader.L4.ShortAdmitReturn
import Leader.L4.ShortHelloAdmitCodec
import Leader.L4.ShortClearLaunch

namespace L4.ShortAdmitGate
set_option maxRecDepth 16384
open AllSizeProtocol PhysicalCustody MISByteCodec ShortResetMIS1Ring ShortResetRow
open ShortResetChart ShortResetCycle ShortResetFlow ShortHelloAdmitCodec
open ShortResetForwardH2 ShortAdmitMIS1Ring ShortAdmitReturn ShortControllerEntrance

variable {s n : Nat} {h : Fin n → Bool}

def GatePacket (C : Chart h) (x : Raw s n) (i race : Nat) : Prop :=
  atGate (header x (nextAt C.root i)) (x (nextAt C.root i)).mis1 (C.route.port i) = true ∧
  bits C.route x i = encode (admitForward false race)

theorem gate_packet_old (C : Chart h) (x : Raw s n) (i race : Nat)
    (L : 1 ≤ race) (U : race ≤ 5) (F : GatePacket C x i race) :
    slot C.route x i = admitForward false race := by
  unfold slot oldK
  dsimp only
  rw [show (kField (C.route.port i)).read (x (nextAt C.route.root i)).mis1 =
    encode (admitForward false race) from F.2,
    show atGate (header x (nextAt C.route.root i)) (x (nextAt C.route.root i)).mis1
      (C.route.port i) = true from F.1,
    decode_admit_forward true false race (by omega)]
  simp [L,U]

private theorem route_link (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q = h q)
    (i : Nat) (I : i+1<C.L) :
    destination (header x (rightNeighbor (nextAt C.root i))) (C.route.port i) =
      some (C.route.port (i+1)) := by
  rw [heads]
  exact C.route.live i I

theorem arrive_gate (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (i : Nat) (I : i+1<C.L)
    (off : atGate (header x (nextAt C.root i)) (x (nextAt C.root i)).mis1 (C.route.port i)=false)
    (on : atGate (header x (nextAt C.root (i+1))) (x (nextAt C.root (i+1))).mis1
      (C.route.port (i+1))=true)
    (F : bits C.route x i = encode (admitForward false 0)) :
    let e := nextAt C.root i
    let y := rawNext s x e
    bits C.route y i = encode T ∧ bits C.route y (i+1) = encode (admitForward false 1) := by
  dsimp only
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have O : slot C.route x i = admitForward false 0 := by
    unfold slot oldK
    dsimp only
    rw [show (kField (C.route.port i)).read (x (nextAt C.route.root i)).mis1 = _ from F,
      show atGate (header x (nextAt C.route.root i)) (x (nextAt C.route.root i)).mis1
        (C.route.port i)=false from off]
    exact (decode_admit_forward false false 0 (by decide)).trans (by decide)
  have A := admit_ungated_out_raw x (nextAt C.root i) (edge_sep N _) _ _ _ (route_link C x heads i I)
    O rfl rfl rfl off
  rw [show rightNeighbor (nextAt C.root i) = nextAt C.root (i+1) from rfl, on] at A
  exact A

theorem parked_out (C : Chart h) (x : Raw s n) (i race : Nat)
    (R : race=1 ∨ race=2) (F : GatePacket C x i race) :
    bits C.route (rawNext s x (nextAt C.root i)) i =
      encode (admitForward false (if race=1 then 3 else 4)) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have O := gate_packet_old C x i race (by rcases R with R|R <;> omega)
    (by rcases R with R|R <;> omega) F
  have A := parked_admit_left_raw x (nextAt C.root i) (edge_sep N _) (C.route.port i)
    (admitForward false race) O rfl rfl rfl F.1 R
  rcases R with rfl|rfl <;> exact A

theorem parked_in (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (i race : Nat) (I : i+1<C.L) (trail : bits C.route x i=encode T)
    (R : race=1 ∨ race=3) (F : GatePacket C x (i+1) race) :
    bits C.route (rawNext s x (nextAt C.root i)) (i+1) =
      encode (admitForward false (if race=1 then 2 else 5)) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have O := gate_packet_old C x (i+1) race (by rcases R with R|R <;> omega)
    (by rcases R with R|R <;> omega) F
  have T0 := slot_of_bits C.route x i T trail_decode trail
  have A := parked_admit_right_raw x (nextAt C.root i) (edge_sep N _) (C.route.port i)
    (C.route.port (i+1)) (route_link C x heads i I)
    (show (slot C.route x i).tag ≠ 2 by rw [T0]; decide)
    (admitForward false race) O rfl rfl rfl F.1 R
  rcases R with rfl|rfl <;> exact A

theorem gate_remote_bits (C : Chart h) (x : Raw s n) (e : Fin n) (i race : Nat)
    (L : e ≠ nextAt C.root i) (R : rightNeighbor e ≠ nextAt C.root i)
    (F : GatePacket C x i race) :
    bits C.route (rawNext s x e) i = encode (admitForward false race) := by
  change (kField (C.route.port i)).read (rawNext s x e (nextAt C.root i)).mis1 = _
  rw [reset_remote_frame_raw _ _ _ (Ne.symm L) (Ne.symm R)]
  exact F.2

theorem ready_exit (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (i : Nat) (I : i+1<C.L) (won : Bool)
    (off : atGate (header x (nextAt C.root (i+1))) (x (nextAt C.root (i+1))).mis1
      (C.route.port (i+1))=false)
    (F : GatePacket C x i (if won then 5 else 4)) :
    let y := rawNext s x (nextAt C.root i)
    bits C.route y i=encode T ∧ bits C.route y (i+1)=encode (admitForward won 0) := by
  dsimp only
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  cases won
  · have O := gate_packet_old C x i 4 (by decide) (by decide) F
    have A := ready_admit_out_raw x (nextAt C.root i) (edge_sep N _) _ _
      (route_link C x heads i I) (admitForward false 4) O rfl rfl rfl F.1 (.inl rfl)
    rw [show rightNeighbor (nextAt C.root i) = nextAt C.root (i+1) from rfl,off] at A
    exact A
  · have O := gate_packet_old C x i 5 (by decide) (by decide) F
    have A := ready_admit_out_raw x (nextAt C.root i) (edge_sep N _) _ _
      (route_link C x heads i I) (admitForward false 5) O rfl rfl rfl F.1 (.inr rfl)
    rw [show rightNeighbor (nextAt C.root i) = nextAt C.root (i+1) from rfl,off] at A
    exact A

/-- At the actual door, the D2 terminal result fixes the source PC and empties K0.
Synchronization and empty remote owned cells are separate flight obligations. -/
theorem root_consume_gate_result (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (phase : get (x C.root).mis1 81 2 (by decide)=2)
    (op : get (x C.root).mis1 78 3 (by decide)=2)
    (won : Bool) (D : bits C.route x 0 = encode (admitReply won)) :
    let y := rawNext s x (RearTrace.predecessor C.root)
    bits C.route y 0=encode E ∧ pc (y C.root).mis1=(if won then 11 else 8) := by
  dsimp only
  let e := RearTrace.predecessor C.root
  have ER : rightNeighbor e=C.root := RearTrace.right_predecessor _
  have H : header x (rightNeighbor e)=true := by rw [ER,heads,C.rootHeader]
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have K : (kField 0).read (x (rightNeighbor e)).mis1 = encode (admitReply won) := by
    rw [ER]
    change (kField (C.route.port 0)).read (x C.root).mis1 = _ at D
    rwa [C.route.rootPort] at D
  have A := consume_admit x e (edge_sep N _) H (by rw [ER]; exact phase) (by rw [ER]; exact op) won K
  dsimp only at A
  rw [ER] at A
  change (kField (C.route.port 0)).read (rawNext s x e C.root).mis1=encode E ∧ _
  rw [C.route.rootPort]
  exact A

end L4.ShortAdmitGate
