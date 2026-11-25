import Leader.L4.ShortWriteCentreWitness
import Leader.L4.ShortWriteAckTransport
import Leader.L4.ShortPublishChart
import Leader.L4.ShortCanonicalReverseChart

namespace L4.ShortWriteChartHop
set_option maxRecDepth 8192
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortWriteCentreWitness ShortWritePacketCodec ShortWriteAckTransport ShortCanonicalReverseChart

def packet (cmd : Cmd) (d : Fin 8) (bad : Bool) : Token :=
  if bad then faultToken 2 else cmd.packet d

def reply (cmd : Cmd) (bad : Bool) : Reply :=
  if bad then Reply.fault else ⟨cmd.ack,by cases cmd <;> rfl,cmd.decode_ack⟩

theorem packet_decode (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true) (bad gate : Bool) :
    decode gate (encode (packet cmd d bad))=packet cmd d bad := by
  cases bad
  · exact cmd.decode_packet d D gate
  · exact (decode_write_faults gate).1

theorem packet_tag (cmd : Cmd) (d : Fin 8) (bad : Bool) : (packet cmd d bad).tag=2 := by
  cases bad <;> cases cmd <;> rfl

theorem packet_opcode (cmd : Cmd) (d : Fin 8) (bad : Bool) :
    (packet cmd d bad).opcode≠2 := by cases bad <;> cases cmd <;> first | exact (by decide : 4≠2) | exact (by decide : 5≠2) | exact (by decide : 0≠2)

theorem packet_fault (cmd : Cmd) (d : Fin 8) (bad : Bool) : (packet cmd d bad).fault=bad := by
  cases bad <;> cases cmd <;> rfl

def advanceBad {s n : Nat} {h : Fin n → Bool} (cmd : Cmd) (d : Fin 8) (C : Chart h)
    (x : Raw s n) (i : Nat) (bad : Bool) : Bool :=
  bad || (i==C.a && !(cmd.accepts (x (nextAt C.root i)).mis1 d))

theorem live_hop {s n : Nat} (x0 x : Raw s n) (X0 : H2Ready x0) (X : H2Ready x)
    (C : Chart (header x0)) (N : 9<n) (heads : ∀ q,header x q=header x0 q)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true) (i : Nat) (I : i+1<C.L)
    (bad : Bool) (wire : bits C.route x i=encode (packet cmd d bad)) :
    let e := nextAt C.root i
    let y := rawNext s x e
    bits C.route y i=encode T ∧
      bits C.route y (i+1)=encode (packet cmd d (advanceBad cmd d C x i bad)) ∧
      (i=C.a → advanceBad cmd d C x i bad=false → CentreEffect cmd d x e) := by
  dsimp only
  let e := nextAt C.root i
  let k := C.route.port (i+1)
  let j := C.route.port i
  have dst := C.actual_dst x heads i (by omega)
  simp only [if_pos I] at dst
  have link : destination (header x (rightNeighbor e)) j=some k := dst
  have K := slot_of_bits C.route x i _ (packet_decode cmd d D bad) wire
  have geom := ShortPublishChart.stage_seal_centre x0 x X0 X C N heads
  have sep := edge_sep (by omega : 1<n) e
  change (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode (packet cmd d (advanceBad cmd d C x i bad)) ∧ _
  cases bad
  · by_cases IC : i=C.a
    · obtain ⟨H,J⟩ := (geom.2.1 i (by omega)).mpr IC
      change j=1 at J
      have O : oldK true (x e).mis1 1=cmd.packet d := by
        change oldK (header x e) (x e).mis1 j=packet cmd d false at K
        rwa [H,J] at K
      have L : destination (header x (rightNeighbor e)) 1=some k := by rwa [J] at link
      obtain ⟨Tt,W,F⟩ := centre_raw_exact cmd d x e sep H k L O
      refine ⟨?_,?_,fun _ B=>F ?_⟩
      · change (kField j).read (rawNext s x e e).mis1=_
        rwa [J]
      · change (kField k).read (rawNext s x e (rightNeighbor e)).mis1=_
        rw [W]
        simp only [advanceBad,IC,beq_self_eq_true,Bool.true_and,Bool.false_or,packet]
        have A : cmd.accepts (x (nextAt C.root C.a)).mis1 d=cmd.accepts (x e).mis1 d :=
          congrArg (fun m => cmd.accepts (x (nextAt C.root m)).mis1 d) IC.symm
        rw [A]
        cases cmd.accepts (x e).mis1 d <;> rfl
      · have BB : (!cmd.accepts (x e).mis1 d)=false := by
          simpa only [advanceBad,e,IC,beq_self_eq_true,Bool.true_and,Bool.false_or] using B
        cases A : cmd.accepts (x e).mis1 d
        · rw [A] at BB; contradiction
        · rfl
    · have F : header x e=false ∨ j≠1 := by
        cases H : header x e
        · exact .inl rfl
        · exact .inr fun J=>IC ((geom.2.1 i (by omega)).mp ⟨H,J⟩)
      have Q := write_ack_forward_raw x e sep j k _ link K (packet_tag cmd d false)
        (.inl ⟨by cases cmd; exact .inl rfl; exact .inr rfl,F⟩)
      refine ⟨Q.1,?_,fun H=>False.elim (IC H)⟩
      have B : (i==C.a)=false := Bool.eq_false_iff.mpr (fun E=>IC (beq_iff_eq.mp E))
      have A : advanceBad cmd d C x i false=false := by simp only [advanceBad,B,Bool.false_and,Bool.false_or]
      rw [A]
      exact Q.2
  · have Q := write_ack_forward_raw x e sep j k _ link K (packet_tag cmd d true)
      (.inr (packet_fault cmd d true))
    refine ⟨Q.1,?_,fun _ H=>False.elim ?_⟩
    · simpa only [advanceBad,Bool.true_or] using Q.2
    · simp [advanceBad] at H

theorem terminal_turn {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (heads : ∀ q,header x q=h q) (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (bad : Bool) (wire : bits C.route x (C.L-1)=encode (packet cmd d bad)) :
    let e := nextAt C.root (C.L-1)
    bits C.route (rawNext s x e) (C.L-1)=encode (reply cmd bad).token := by
  let i := C.L-1
  let e := nextAt C.root i
  have I : i<C.L := by have := C.positive; omega
  have I' : ¬ i+1<C.L := by have := C.positive; omega
  have sep := edge_sep (by have := C.positive; have := C.length_lt; omega : 1<n) e
  have K := slot_of_bits C.route x i _ (packet_decode cmd d D bad) wire
  have dst := C.actual_dst x heads i I
  simp only [if_neg I'] at dst
  have Q := write_ack_turn_raw x e sep _ _ dst K (packet_tag cmd d bad)
    (by cases bad
        · cases cmd
          · exact .inl rfl
          · exact .inr (.inl rfl)
        · exact .inr (.inr rfl))
  exact Q.trans (by cases cmd <;> cases bad <;> rfl)

#print axioms packet_decode
#print axioms packet_tag
#print axioms packet_opcode
#print axioms packet_fault
#print axioms live_hop
#print axioms terminal_turn
-- CHECK: ShortWriteChartHop.lean:37; original opens and options unchanged.
theorem live_hop_fixed {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (C : Chart h) (N : 9<n) (heads : ∀ q, header x q=h q)
    (geom : C.a+1<C.L ∧
      ∀ k, k<C.L →
        (header x (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a))
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true) (i : Nat) (I : i+1<C.L)
    (bad : Bool) (wire : bits C.route x i=encode (packet cmd d bad)) :
    let e := nextAt C.root i
    let y := rawNext s x e
    bits C.route y i=encode T ∧
      bits C.route y (i+1)=encode (packet cmd d (advanceBad cmd d C x i bad)) ∧
      (i=C.a → advanceBad cmd d C x i bad=false → CentreEffect cmd d x e) := by
  dsimp only
  let e := nextAt C.root i
  let k := C.route.port (i+1)
  let j := C.route.port i
  have dst := C.actual_dst x heads i (by omega)
  simp only [if_pos I] at dst
  have link : destination (header x (rightNeighbor e)) j=some k := dst
  have K := slot_of_bits C.route x i _ (packet_decode cmd d D bad) wire
  have sep := edge_sep (by omega : 1<n) e
  change (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode (packet cmd d (advanceBad cmd d C x i bad)) ∧ _
  cases bad
  · by_cases IC : i=C.a
    · obtain ⟨H,J⟩ := (geom.2 i (by omega)).mpr IC
      change j=1 at J
      have O : oldK true (x e).mis1 1=cmd.packet d := by
        change oldK (header x e) (x e).mis1 j=packet cmd d false at K
        rwa [H,J] at K
      have L : destination (header x (rightNeighbor e)) 1=some k := by rwa [J] at link
      obtain ⟨Tt,W,F⟩ := centre_raw_exact cmd d x e sep H k L O
      refine ⟨?_,?_,fun _ B=>F ?_⟩
      · change (kField j).read (rawNext s x e e).mis1=_
        rwa [J]
      · change (kField k).read (rawNext s x e (rightNeighbor e)).mis1=_
        rw [W]
        simp only [advanceBad,IC,beq_self_eq_true,Bool.true_and,Bool.false_or,packet]
        have A : cmd.accepts (x (nextAt C.root C.a)).mis1 d=cmd.accepts (x e).mis1 d :=
          congrArg (fun m => cmd.accepts (x (nextAt C.root m)).mis1 d) IC.symm
        rw [A]
        cases cmd.accepts (x e).mis1 d <;> rfl
      · have BB : (!cmd.accepts (x e).mis1 d)=false := by
          simpa only [advanceBad,e,IC,beq_self_eq_true,Bool.true_and,Bool.false_or] using B
        cases A : cmd.accepts (x e).mis1 d
        · rw [A] at BB; contradiction
        · rfl
    · have F : header x e=false ∨ j≠1 := by
        cases H : header x e
        · exact .inl rfl
        · exact .inr fun J=>IC ((geom.2 i (by omega)).mp ⟨H,J⟩)
      have Q := write_ack_forward_raw x e sep j k _ link K (packet_tag cmd d false)
        (.inl ⟨by cases cmd; exact .inl rfl; exact .inr rfl,F⟩)
      refine ⟨Q.1,?_,fun H=>False.elim (IC H)⟩
      have B : (i==C.a)=false := Bool.eq_false_iff.mpr (fun E=>IC (beq_iff_eq.mp E))
      have A : advanceBad cmd d C x i false=false := by simp only [advanceBad,B,Bool.false_and,Bool.false_or]
      rw [A]
      exact Q.2
  · have Q := write_ack_forward_raw x e sep j k _ link K (packet_tag cmd d true)
      (.inr (packet_fault cmd d true))
    refine ⟨Q.1,?_,fun _ H=>False.elim ?_⟩
    · simpa only [advanceBad,Bool.true_or] using Q.2
    · simp [advanceBad] at H

#print axioms live_hop_fixed
end L4.ShortWriteChartHop
