import Leader.L4.ShortWriteChartHop
import Leader.L4.ShortCommitFlightRaw

namespace L4.ShortCommitChartHop
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortWritePacketCodec ShortCanonicalReverseChart

inductive Status where
  | pending | applied | failed
  deriving DecidableEq

def packet (d : Fin 8) : Status → Token
  | .pending => writeFwd 6 d false
  | .applied => writeFwd 6 d true
  | .failed => faultToken 2

def reply : Status → Reply
  | .applied => ⟨writeAck 6,rfl,fun g=>decode_write_ack g 6 (by decide) (by decide)⟩
  | _ => Reply.fault

theorem packet_decode (d : Fin 8) (D : descValid d.val=true) (p : Status) (g : Bool) :
    decode g (encode (packet d p))=packet d p := by
  cases p
  · exact decode_write_forward g 6 d false (by decide) (by decide) D
  · exact decode_write_forward g 6 d true (by decide) (by decide) D
  · exact (decode_write_faults g).1

theorem packet_tag (d : Fin 8) (p : Status) : (packet d p).tag=2 := by cases p <;> rfl

theorem packet_opcode (d : Fin 8) (p : Status) : (packet d p).opcode≠2 := by
  cases p
  · exact (by decide : 6≠2)
  · exact (by decide : 6≠2)
  · exact (by decide : 0≠2)

def advance {s n : Nat} {h : Fin n → Bool} (d : Fin 8) (C : Chart h)
    (x : Raw s n) (i : Nat) (p : Status) : Status :=
  if i=C.a-1 then
    if p=.pending ∧ commitAccept (x (rightNeighbor (nextAt C.root i))).mis1 (packet d p)=true
    then .applied else .failed
  else p

def Publication {s n : Nat} (d : Fin 8) (x : Raw s n) (e : Fin n) : Prop :=
  commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false)=true ∧
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92=(d.val/2%2==1)

theorem live_hop {s n : Nat} (x0 x : Raw s n) (X0 : H2Ready x0)
    (C : Chart (header x0)) (N : 9<n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true) (i : Nat) (I : i+1<C.L)
    (p : Status) (wire : bits C.route x i=encode (packet d p)) :
    let e := nextAt C.root i
    let y := rawNext s x e
    bits C.route y i=encode T ∧
      bits C.route y (i+1)=encode (packet d (advance d C x i p)) ∧
      (i=C.a-1 → advance d C x i p=.applied → Publication d x e) := by
  dsimp only
  let e := nextAt C.root i
  let j := C.route.port i
  let k := C.route.port (i+1)
  have sep := edge_sep (by omega : 1<n) e
  have dst := C.actual_dst x heads i (by omega)
  simp only [if_pos I] at dst
  have L : destination (header x (rightNeighbor e)) j=some k := dst
  have W : (kField j).read (x e).mis1=encode (packet d p) := wire
  have O := slot_of_bits C.route x i _ (packet_decode d D p) wire
  have geo := (ShortPublishChart.commit_centre x0 x X0 C N heads).2.2.1 i I
  change (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode (packet d (advance d C x i p)) ∧ _
  by_cases same : i=C.a-1
  · obtain ⟨H,J,K⟩ := geo.mpr same
    change j=0 at J
    change k=1 at K
    rw [J,K]
    cases p with
    | failed =>
      have F := ShortCommitFlightRaw.fault_relay_raw x e sep j k L O
      rw [J,K] at F
      simpa [advance,same,packet] using F
    | applied =>
      have G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d true)=false := by
        simp [commitAccept,writeFwd]
      have F := ShortCommitFlightRaw.canonical_centre_rejected_raw x e sep H d true D
        (J ▸ W) G
      simpa [advance,same,packet] using And.intro F.1 F.2.1
    | pending =>
      have E : commitAccept (x (rightNeighbor (nextAt C.root i))).mis1 (packet d .pending) =
          commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false) := rfl
      by_cases G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false)=true
      · have F := ShortCommitFlightRaw.canonical_centre_publication_raw x e sep H d D (J ▸ W) G
        refine ⟨F.1,?_,fun _ _=>⟨G,F.2.2.2⟩⟩
        have P : advance d C x i .pending=.applied := by
          unfold advance
          rw [if_pos same,E,if_pos ⟨rfl,G⟩]
        rw [P]
        exact F.2.1
      · have F := ShortCommitFlightRaw.canonical_centre_rejected_raw x e sep H d false D
          (J ▸ W) (Bool.eq_false_iff.mpr G)
        have P : advance d C x i .pending=.failed := by
          unfold advance
          rw [if_pos same,E,if_neg (fun Y=>G Y.2)]
        rw [P]
        exact ⟨F.1,F.2.1,fun _ Y=>by contradiction⟩
  · have nc : ¬(header x (rightNeighbor e)=true ∧ j=0 ∧ k=1) :=
      fun P => same (geo.mp P)
    cases p with
    | failed =>
      have F := ShortCommitFlightRaw.fault_relay_raw x e sep j k L O
      simpa [advance,same,packet] using F
    | pending =>
      have F := ShortCommitFlightRaw.canonical_relay_raw x e sep j k L nc d false D W
      simpa [advance,same,packet] using And.intro F.1 F.2.1
    | applied =>
      have F := ShortCommitFlightRaw.canonical_relay_raw x e sep j k L nc d true D W
      simpa [advance,same,packet] using And.intro F.1 F.2.1

theorem terminal_turn {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ q,header x q=h q) (d : Fin 8) (D : descValid d.val=true)
    (p : Status) (wire : bits C.route x (C.L-1)=encode (packet d p)) :
    let e := nextAt C.root (C.L-1)
    bits C.route (rawNext s x e) (C.L-1)=encode (reply p).token := by
  let i := C.L-1
  let e := nextAt C.root i
  have I : i<C.L := by have := C.positive; omega
  have I' : ¬ i+1<C.L := by have := C.positive; omega
  have sep := edge_sep (by have := C.positive; have := C.length_lt; omega : 1<n) e
  have K := slot_of_bits C.route x i _ (packet_decode d D p) wire
  have dst := C.actual_dst x heads i I
  simp only [if_neg I'] at dst
  cases p with
  | failed => exact ShortCommitFlightRaw.fault_turn_raw x e sep _ dst K
  | pending => exact ShortCommitFlightRaw.canonical_terminal_raw x e sep _ dst d false D wire
  | applied => exact ShortCommitFlightRaw.canonical_terminal_raw x e sep _ dst d true D wire

#print axioms live_hop
#print axioms terminal_turn
-- CHECK: ShortCommitChartHop.lean:50; original opens and options unchanged.
theorem live_hop_fixed {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (C : Chart h) (N : 9<n) (heads : ∀ q, header x q=h q)
    (geom : C.a-1+1<C.L ∧
      ∀ k, k+1<C.L →
        (header x (rightNeighbor (nextAt C.root k))=true ∧
          C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1))
    (d : Fin 8) (D : descValid d.val=true) (i : Nat) (I : i+1<C.L)
    (p : Status) (wire : bits C.route x i=encode (packet d p)) :
    let e := nextAt C.root i
    let y := rawNext s x e
    bits C.route y i=encode T ∧
      bits C.route y (i+1)=encode (packet d (advance d C x i p)) ∧
      (i=C.a-1 → advance d C x i p=.applied → Publication d x e) := by
  dsimp only
  let e := nextAt C.root i
  let j := C.route.port i
  let k := C.route.port (i+1)
  have sep := edge_sep (by omega : 1<n) e
  have dst := C.actual_dst x heads i (by omega)
  simp only [if_pos I] at dst
  have L : destination (header x (rightNeighbor e)) j=some k := dst
  have W : (kField j).read (x e).mis1=encode (packet d p) := wire
  have O := slot_of_bits C.route x i _ (packet_decode d D p) wire
  have geo := geom.2 i I
  change (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode (packet d (advance d C x i p)) ∧ _
  by_cases same : i=C.a-1
  · obtain ⟨H,J,K⟩ := geo.mpr same
    change j=0 at J
    change k=1 at K
    rw [J,K]
    cases p with
    | failed =>
      have F := ShortCommitFlightRaw.fault_relay_raw x e sep j k L O
      rw [J,K] at F
      simpa [advance,same,packet] using F
    | applied =>
      have G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d true)=false := by
        simp [commitAccept,writeFwd]
      have F := ShortCommitFlightRaw.canonical_centre_rejected_raw x e sep H d true D
        (J ▸ W) G
      simpa [advance,same,packet] using And.intro F.1 F.2.1
    | pending =>
      have E : commitAccept (x (rightNeighbor (nextAt C.root i))).mis1 (packet d .pending) =
          commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false) := rfl
      by_cases G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false)=true
      · have F := ShortCommitFlightRaw.canonical_centre_publication_raw x e sep H d D (J ▸ W) G
        refine ⟨F.1,?_,fun _ _=>⟨G,F.2.2.2⟩⟩
        have P : advance d C x i .pending=.applied := by
          unfold advance
          rw [if_pos same,E,if_pos ⟨rfl,G⟩]
        rw [P]
        exact F.2.1
      · have F := ShortCommitFlightRaw.canonical_centre_rejected_raw x e sep H d false D
          (J ▸ W) (Bool.eq_false_iff.mpr G)
        have P : advance d C x i .pending=.failed := by
          unfold advance
          rw [if_pos same,E,if_neg (fun Y=>G Y.2)]
        rw [P]
        exact ⟨F.1,F.2.1,fun _ Y=>by contradiction⟩
  · have nc : ¬(header x (rightNeighbor e)=true ∧ j=0 ∧ k=1) :=
      fun P => same (geo.mp P)
    cases p with
    | failed =>
      have F := ShortCommitFlightRaw.fault_relay_raw x e sep j k L O
      simpa [advance,same,packet] using F
    | pending =>
      have F := ShortCommitFlightRaw.canonical_relay_raw x e sep j k L nc d false D W
      simpa [advance,same,packet] using And.intro F.1 F.2.1
    | applied =>
      have F := ShortCommitFlightRaw.canonical_relay_raw x e sep j k L nc d true D W
      simpa [advance,same,packet] using And.intro F.1 F.2.1

#print axioms live_hop_fixed
end L4.ShortCommitChartHop
