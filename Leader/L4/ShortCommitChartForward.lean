import Leader.L4.ShortCommitChartHop
import Leader.L4.ShortInboundFrame
import Leader.L4.ShortHelloForward
import Leader.L4.ShortClearLaunch

namespace L4.ShortCommitChartForward
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortCommitChartHop ShortCanonicalReverseChart

private theorem safe_wire (d : Fin 8) (p : Status) {t : Token}
    (A : t=packet d p ∨ t=T) : InboundToken t := by
  rcases A with H|H
  · rw [H]
    exact ⟨.inr (packet_tag d p),.inr (packet_opcode d p)⟩
  · rw [H]
    exact ⟨.inl rfl,.inr (by decide : 0≠2)⟩

theorem forward_step {s n : Nat} (x0 x : Raw s n) (X0 : H2Ready x0)
    (C : Chart (header x0)) (N : 9<n) (e : Fin n)
    (heads : ∀ q, header x q=header x0 q) (d : Fin 8)
    (p : Status) (D : descValid d.val=true)
    (wait : get (x C.root).mis1 81 2 (by decide)=2)
    (op : get (x C.root).mis1 78 3 (by decide)=6)
    (i : Nat) (I : i<C.L)
    (trails : TrailPrefix C.route x i) (front : bits C.route x i=encode (packet d p)) :
    let y := rawNext s x e
    TrailPrefix C.route y i ∧
      (if e=nextAt C.root i then
        if i+1<C.L then
          bits C.route y i=encode T ∧
            bits C.route y (i+1)=encode (packet d (advance d C x i p)) ∧
            (i=C.a-1 → advance d C x i p=.applied → Publication d x e)
        else bits C.route y i=encode (reply p).token
      else bits C.route y i=encode (packet d p)) := by
  dsimp only
  let R := C.route
  have RL : R.length=C.L := rfl
  let y := rawNext s x e
  have sep := edge_sep (by omega : 1<n) e
  have Tf j J := slot_of_bits R x j T trail_decode (trails j J)
  have Ff := slot_of_bits R x i (packet d p) (packet_decode d D p) front
  have canonical (j : Nat) (J : j≤i) : encode (slot R x j)=bits R x j := by
    rcases Nat.eq_or_lt_of_le J with H|H
    · subst j
      rw [Ff,front]
    · rw [Tf j H,trails j H]
  have rootWire : encode (oldK true (x R.root).mis1 0)=(kField 0).read (x R.root).mis1 := by
    have K := canonical 0 (by omega)
    have H := (heads R.root).trans R.rootHeader
    simpa only [slot,bits,nextAt,H,R.rootPort] using K
  change TrailPrefix R y i ∧
      (if e=nextAt R.root i then
        if i+1<R.length then
          bits R y i=encode T ∧ bits R y (i+1)=encode (packet d (advance d C x i p)) ∧
             (i=C.a-1 → advance d C x i p=.applied → Publication d x e)
        else bits R y i=encode (reply p).token
      else bits R y i=encode (packet d p))
  have dst (j : Nat) (J : j+1<R.length) :
      destination (header x (rightNeighbor (nextAt R.root j))) (R.port j)=some (R.port (j+1)) := by
    rw [heads]
    exact R.live j J
  have predecessor (j : Nat) (J : 0<j) (h : rightNeighbor e=nextAt R.root j) :
      e=nextAt R.root (j-1) := by
    have E : rightNeighbor (nextAt R.root (j-1))=nextAt R.root j := by
      rw [show j=j-1+1 by omega]; rfl
    have E2 := congrArg RearTrace.predecessor (h.trans E.symm)
    simpa only [RearTrace.predecessor_right] using E2
  have hold_in (j : Nat) (J : j≤i)
      (h' : rightNeighbor e=nextAt R.root j)
      (safe : slot R x j=packet d p ∨ slot R x j=T) :
      (kField (R.port j)).read (y (nextAt R.root j)).mis1=
      (kField (R.port j)).read (x (nextAt R.root j)).mis1 := by
    by_cases zero : j=0
    · subst j
      change rightNeighbor e=R.root at h'
      rw [R.rootPort]
      have hd : header x (rightNeighbor e)=true := by rw [h',heads,R.rootHeader]
      rw [←h']
      have hs : header x R.root=true := by rw [heads,R.rootHeader]
      have S : oldK true (x (rightNeighbor e)).mis1 0=packet d p ∨
          oldK true (x (rightNeighbor e)).mis1 0=T := by
        rw [h',←R.rootPort,←hs]
        exact safe
      have RAW : encode (oldK true (x (rightNeighbor e)).mis1 0)=
          (kField 0).read (x (rightNeighbor e)).mis1 := by
        rw [h']
        exact rootWire
      exact ShortInboundFrame.root_frame_raw x e sep hd (by rw [h']; exact wait)
        (by rw [h']; change get (x C.root).mis1 78 3 (by decide)<7; rw [op]; decide) (safe_wire d p S) (fun _=>RAW)
    · let pred := j-1
      have ep : e=nextAt R.root pred := predecessor j (Nat.pos_of_ne_zero zero) h'
      have P : pred+1=j := by dsimp [pred]; omega
      have link : destination (header x (rightNeighbor e)) (R.port pred)=some (R.port j) := by
        rw [ep,←P]
        have H := dst pred (by omega)
        rwa [P] at H ⊢
      rw [←h']
      apply ShortInboundFrame.inbound_frame_raw x e sep (R.port pred) _ link
      · rw [ep]
        exact Tf pred (by omega)
      · rw [h']
        exact safe_wire d p safe
      · rw [h']
        exact fun _ => canonical j J
  constructor
  · intro j J
    have jt := Tf j J
    apply Eq.trans _ (trails j J)
    unfold bits
    by_cases L : nextAt R.root j=e
    · have K : j+1≤i := by omega
      have safe : slot R x (j+1)=packet d p ∨ slot R x (j+1)=T := by
        rcases Nat.eq_or_lt_of_le K with E|E
        · exact .inl (E.symm ▸ Ff)
        · exact .inr (Tf _ E)
      have H := ShortInboundFrame.prefix_frame_raw x e sep (R.port j) (R.port (j+1))
        (by rw [←L]; exact dst j (by omega))
        (by rw [←L]; exact jt)
        (by rw [←L]; exact safe_wire d p safe)
      rw [L]
      exact H
    · by_cases K : nextAt R.root j=rightNeighbor e
      · exact hold_in j (by omega) K.symm (.inr jt)
      · have F := reset_remote_frame_raw x e (nextAt R.root j) L K
        exact congrArg ((kField (R.port j)).read) F
  · split
    · rename_i E
      subst e
      split
      · rename_i J
        exact live_hop x0 x X0 C N heads d D i J p front
      · rename_i J
        have E : i=R.length-1 := by omega
        subst i
        exact terminal_turn C x heads d D p front
    · rename_i E
      apply Eq.trans _ front
      unfold bits
      by_cases K : nextAt R.root i=rightNeighbor e
      · exact hold_in i (by omega) K.symm (.inl Ff)
      · have F := reset_remote_frame_raw x e (nextAt R.root i) (Ne.symm E) K
        exact congrArg ((kField (R.port i)).read) F

-- CHECK: ShortCommitChartForward.lean:21; original opens and options unchanged.
theorem forward_step_fixed {s n : Nat} {h : Fin n → Bool} (x : Raw s n)
    (C : Chart h) (N : 9<n) (e : Fin n)
    (heads : ∀ q, header x q=h q)
    (geom : C.a-1+1<C.L ∧
      ∀ k, k+1<C.L →
        (header x (rightNeighbor (nextAt C.root k))=true ∧
          C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1)) (d : Fin 8)
    (p : Status) (D : descValid d.val=true)
    (wait : get (x C.root).mis1 81 2 (by decide)=2)
    (op : get (x C.root).mis1 78 3 (by decide)=6)
    (i : Nat) (I : i<C.L)
    (trails : TrailPrefix C.route x i) (front : bits C.route x i=encode (packet d p)) :
    let y := rawNext s x e
    TrailPrefix C.route y i ∧
      (if e=nextAt C.root i then
        if i+1<C.L then
          bits C.route y i=encode T ∧
            bits C.route y (i+1)=encode (packet d (advance d C x i p)) ∧
            (i=C.a-1 → advance d C x i p=.applied → Publication d x e)
        else bits C.route y i=encode (reply p).token
      else bits C.route y i=encode (packet d p)) := by
  dsimp only
  let R := C.route
  have RL : R.length=C.L := rfl
  let y := rawNext s x e
  have sep := edge_sep (by omega : 1<n) e
  have Tf j J := slot_of_bits R x j T trail_decode (trails j J)
  have Ff := slot_of_bits R x i (packet d p) (packet_decode d D p) front
  have canonical (j : Nat) (J : j≤i) : encode (slot R x j)=bits R x j := by
    rcases Nat.eq_or_lt_of_le J with H|H
    · subst j
      rw [Ff,front]
    · rw [Tf j H,trails j H]
  have rootWire : encode (oldK true (x R.root).mis1 0)=(kField 0).read (x R.root).mis1 := by
    have K := canonical 0 (by omega)
    have H := (heads R.root).trans R.rootHeader
    simpa only [slot,bits,nextAt,H,R.rootPort] using K
  change TrailPrefix R y i ∧
      (if e=nextAt R.root i then
        if i+1<R.length then
          bits R y i=encode T ∧ bits R y (i+1)=encode (packet d (advance d C x i p)) ∧
             (i=C.a-1 → advance d C x i p=.applied → Publication d x e)
        else bits R y i=encode (reply p).token
      else bits R y i=encode (packet d p))
  have dst (j : Nat) (J : j+1<R.length) :
      destination (header x (rightNeighbor (nextAt R.root j))) (R.port j)=some (R.port (j+1)) := by
    rw [heads]
    exact R.live j J
  have predecessor (j : Nat) (J : 0<j) (h : rightNeighbor e=nextAt R.root j) :
      e=nextAt R.root (j-1) := by
    have E : rightNeighbor (nextAt R.root (j-1))=nextAt R.root j := by
      rw [show j=j-1+1 by omega]; rfl
    have E2 := congrArg RearTrace.predecessor (h.trans E.symm)
    simpa only [RearTrace.predecessor_right] using E2
  have hold_in (j : Nat) (J : j≤i)
      (h' : rightNeighbor e=nextAt R.root j)
      (safe : slot R x j=packet d p ∨ slot R x j=T) :
      (kField (R.port j)).read (y (nextAt R.root j)).mis1=
      (kField (R.port j)).read (x (nextAt R.root j)).mis1 := by
    by_cases zero : j=0
    · subst j
      change rightNeighbor e=R.root at h'
      rw [R.rootPort]
      have hd : header x (rightNeighbor e)=true := by rw [h',heads,R.rootHeader]
      rw [←h']
      have hs : header x R.root=true := by rw [heads,R.rootHeader]
      have S : oldK true (x (rightNeighbor e)).mis1 0=packet d p ∨
          oldK true (x (rightNeighbor e)).mis1 0=T := by
        rw [h',←R.rootPort,←hs]
        exact safe
      have RAW : encode (oldK true (x (rightNeighbor e)).mis1 0)=
          (kField 0).read (x (rightNeighbor e)).mis1 := by
        rw [h']
        exact rootWire
      exact ShortInboundFrame.root_frame_raw x e sep hd (by rw [h']; exact wait)
        (by rw [h']; change get (x C.root).mis1 78 3 (by decide)<7; rw [op]; decide) (safe_wire d p S) (fun _=>RAW)
    · let pred := j-1
      have ep : e=nextAt R.root pred := predecessor j (Nat.pos_of_ne_zero zero) h'
      have P : pred+1=j := by dsimp [pred]; omega
      have link : destination (header x (rightNeighbor e)) (R.port pred)=some (R.port j) := by
        rw [ep,←P]
        have H := dst pred (by omega)
        rwa [P] at H ⊢
      rw [←h']
      apply ShortInboundFrame.inbound_frame_raw x e sep (R.port pred) _ link
      · rw [ep]
        exact Tf pred (by omega)
      · rw [h']
        exact safe_wire d p safe
      · rw [h']
        exact fun _ => canonical j J
  constructor
  · intro j J
    have jt := Tf j J
    apply Eq.trans _ (trails j J)
    unfold bits
    by_cases L : nextAt R.root j=e
    · have K : j+1≤i := by omega
      have safe : slot R x (j+1)=packet d p ∨ slot R x (j+1)=T := by
        rcases Nat.eq_or_lt_of_le K with E|E
        · exact .inl (E.symm ▸ Ff)
        · exact .inr (Tf _ E)
      have H := ShortInboundFrame.prefix_frame_raw x e sep (R.port j) (R.port (j+1))
        (by rw [←L]; exact dst j (by omega))
        (by rw [←L]; exact jt)
        (by rw [←L]; exact safe_wire d p safe)
      rw [L]
      exact H
    · by_cases K : nextAt R.root j=rightNeighbor e
      · exact hold_in j (by omega) K.symm (.inr jt)
      · have F := reset_remote_frame_raw x e (nextAt R.root j) L K
        exact congrArg ((kField (R.port j)).read) F
  · split
    · rename_i E
      subst e
      split
      · rename_i J
        exact ShortCommitChartHop.live_hop_fixed x C N heads geom d D i J p front
      · rename_i J
        have E : i=R.length-1 := by omega
        subst i
        exact terminal_turn C x heads d D p front
    · rename_i E
      apply Eq.trans _ front
      unfold bits
      by_cases K : nextAt R.root i=rightNeighbor e
      · exact hold_in i (by omega) K.symm (.inl Ff)
      · have F := reset_remote_frame_raw x e (nextAt R.root i) (Ne.symm E) K
        exact congrArg ((kField (R.port i)).read) F

end L4.ShortCommitChartForward
