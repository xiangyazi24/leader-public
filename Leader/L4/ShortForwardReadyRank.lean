import Leader.L4.ShortForwardRank
import Leader.L4.ShortForwardMIS1Ring

namespace L4.ShortForwardReadyRank
open MISByteCodec PhysicalCustody AllSizeProtocol
open ShortResetCycle ShortResetForwardH2 ShortResetChart ShortResetWatch
open ShortResetMIS1Ring ShortResetRow ShortForwardMIS1Ring ShortForwardRank
open ShortResetFlow

/-- For raw chart updates the two participant slots are the only ones
that can change decoded tokens, when external physical headers are frozen. -/
theorem remote_slot {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (j : Nat)
    (Hx : ∀ q, header x q=h q) (Hy : ∀ q, header (rawNext s x e) q=h q)
    (E : nextAt C.root j≠e) (R : nextAt C.root j≠rightNeighbor e) :
    slot C.route (rawNext s x e) j=slot C.route x j := by
  unfold slot
  dsimp only
  change oldK (header (rawNext s x e) (nextAt C.root j))
    ((rawNext s x e) (nextAt C.root j)).mis1 (C.route.port j)=_
  rw [Hy,Hx,reset_remote_frame_raw _ _ _ E R]
  rfl

theorem chart_except {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (i j : Nat) (I : i<C.L) (J : j<C.L)
    (Hx : ∀ q, header x q=h q)
    (Hy : ∀ q, header (rawNext s x (nextAt C.root i)) q=h q)
    (A : j≠i) (B : j≠i+1) :
    slot C.route (rawNext s x (nextAt C.root i)) j=slot C.route x j := by
  apply remote_slot C x _ j Hx Hy
  · exact fun E=>A (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)
  · change nextAt C.root j≠nextAt C.root (i+1)
    exact fun E=>B (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)

/-- A selected ready-forward outgoing mark strictly decreases the
physical forward score, whether it advances or turns at the terminal. -/
theorem ready_descent {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (i : Fin C.L)
    (Hx : ∀ q, header x q=h q)
    (Hy : ∀ q, header (rawNext s x (nextAt C.root i.val)) q=h q)
    (F : (slot C.route x i.val).tag=2)
    (ready : let e:=nextAt C.root i.val
      forwardReady (header x e) (x e).mis1 (C.route.port i.val)=true) :
    physicalScore C (rawNext s x (nextAt C.root i.val)) < physicalScore C x := by
  let e := nextAt C.root i.val
  let y := rawNext s x e
  have L := C.length_lt
  have I := i.isLt
  have sep : e≠rightNeighbor e := edge_sep (by omega) e
  have D := C.actual_dst x Hx i.val I
  rw [physicalScore_eq C _ Hy,physicalScore_eq C _ Hx]
  have other (j : Fin C.L) (A : j.val≠i.val) (B : j.val≠i.val+1) :
      localScore C.L j.val (slot C.route y j.val)=
        localScore C.L j.val (slot C.route x j.val) :=
    congrArg (localScore C.L j.val) (chart_except C x i.val j.val I j.isLt Hx Hy A B)
  by_cases K : i.val+1<C.L
  · let b : Fin C.L := ⟨i.val+1,K⟩
    have d : destination (header x (rightNeighbor e)) (C.route.port i.val)
        =some (C.route.port b.val) := by
      simpa only [Chart.route,if_pos K] using D
    have E := inherited_ready_out_raw x e sep _ _ d ready
    have NF : (slot C.route y i.val).tag≠2 := by
      change (decode _ ((kField (C.route.port i.val)).read (y e).mis1)).tag≠2
      rw [E.1,trail_decode]
      decide
    exact transport_lt i b rfl F NF (fun j A B => other j
      (fun Q=>A (Fin.ext Q)) (fun Q=>B (Fin.ext Q)))
  · have d : destination (header x (rightNeighbor e)) (C.route.port i.val)=none := by
      simpa only [Chart.route,if_neg K] using D
    have E : (slot C.route y i.val).tag=3 := inherited_ready_turn_raw x e sep _ d ready
    exact turn_lt i F (by change (slot C.route y i.val).tag≠2; omega) (fun j A => other j (fun Q=>A (Fin.ext Q))
      (by have := j.isLt; omega))

#print axioms remote_slot
#print axioms chart_except
#print axioms ready_descent

end L4.ShortForwardReadyRank
