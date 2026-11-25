import Leader.L4.WidthWaitDrain
import Leader.L4.WidthTokenTransport

namespace L4.WidthWaitLiteralTags

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

open AllSizeProtocol WidthByteRows WidthChecksum WidthTokenTransport
open WidthWaitDrain (Tag)

def tagOf (k : Nat) : Tag :=
  match k with
  | 0 => .E
  | 1 => .T
  | 2 => .F
  | _ => .D

def observe {c : Nat} (x : BitVec (W c)) : Tag := tagOf (packet (c:=c) x).tag

theorem encode_tag (t : Token) (T : t.tag<4) (O : t.op<8) (A : t.arg<16) :
    (decode (encode t)).tag=t.tag := by
  rw [decode_tag]
  unfold encode
  rw [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  cases t.fault <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> split <;> omega

private theorem bit2 (b : Bool) : b.toNat≤1 := by cases b <;> decide

private theorem decoded_small (x : BitVec 16) :
    (decode x).tag<4 ∧ (decode x).op<8 ∧ (decode x).arg<16 := by
  have T : (x.extractLsb' 14 2).toNat<4 := (x.extractLsb' 14 2).isLt
  have O : (x.extractLsb' 10 3).toNat<8 := (x.extractLsb' 10 3).isLt
  have A : (x.extractLsb' 0 4).toNat<16 := (x.extractLsb' 0 4).isLt
  unfold decode faultCode
  dsimp only
  split
  · exact ⟨T,by exact (by decide : (0:Nat)<8),by exact (by decide : (0:Nat)<16)⟩
  split
  · exact ⟨T,by exact (by decide : (0:Nat)<8),by exact (by decide : (0:Nat)<16)⟩
  refine ⟨T,O,?_⟩
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) A

private theorem cmp4 (b x fallback : Nat) (H : fallback<4) :
    (if b<x then 1 else if x<b then 2 else fallback)<4 := by
  split
  · decide
  split
  · decide
  · exact H

private theorem departing_small {c : Nat} (r i : Nat) (x : BitVec (W c))
    (t : Token) (A : t.arg<16) :
    let t' := (departing r i x t).2
    t'.tag=t.tag ∧ t'.op=t.op ∧ t'.arg<16 := by
  unfold departing
  dsimp only
  split
  · exact ⟨rfl,rfl,A⟩
  split
  · exact ⟨rfl,rfl,A⟩
  · refine ⟨rfl,rfl,?_⟩
    apply Nat.or_lt_two_pow (n:=4) A
    split <;> decide
  · split
    · refine ⟨rfl,rfl,?_⟩
      have U := cmp4 (get (c:=c) x 5 1 (by decide)) ((r >>> i)%2) (t.arg/4) (by omega)
      have V := cmp4 (get (c:=c) x 5 1 (by decide)) (((r-1) >>> i)%2) (t.arg%4) (by omega)
      dsimp only
      omega
    · exact ⟨rfl,rfl,A⟩
  · split <;> exact ⟨rfl,rfl,A⟩
  · split
    · refine ⟨rfl,rfl,?_⟩
      have G : get (c:=c) x 5 1 (by decide)<2 := ((suffixField c 5 1 (by decide)).read x).isLt
      dsimp only
      omega
    · exact ⟨rfl,rfl,A⟩
  · exact ⟨rfl,rfl,A⟩
  · exact ⟨rfl,rfl,A⟩

private theorem finish_small (t : Token) (O : t.op<8) (A : t.arg<16) :
    (finish t).tag=3 ∧ (finish t).op<8 ∧ (finish t).arg<16 := by
  unfold finish faultCode
  split
  · decide
  refine ⟨rfl,O,?_⟩
  split
  · exact A
  split
  · have S := bit2 (t.arg/4==1)
    have T := bit2 (t.arg%4==0)
    dsimp only
    omega
  · exact (by decide : (0:Nat)<16)

private theorem packet_transport {c : Nat} (x : BitVec (W c)) :
    (decode (encode (packet (c:=c) x))).tag=(packet (c:=c) x).tag := by
  have H := decoded_small (wire (c:=c) x)
  exact encode_tag _ H.1 H.2.1 H.2.2

private theorem depart_transport {c : Nat} (r i : Nat) (x : BitVec (W c)) :
    let t := (departing (c:=c) r i x (packet (c:=c) x)).2
    (decode (encode t)).tag=(packet (c:=c) x).tag ∧
      (decode (encode (finish t))).tag=3 := by
  let t := (departing (c:=c) r i x (packet (c:=c) x)).2
  have H := decoded_small (wire (c:=c) x)
  have G := departing_small r i x (packet (c:=c) x) H.2.2
  change t.tag=(packet (c:=c) x).tag ∧ t.op=(packet (c:=c) x).op ∧ t.arg<16 at G
  have O : t.op<8 := G.2.1.symm ▸ H.2.1
  have J := finish_small t O G.2.2
  have T : t.tag<4 := G.1.symm ▸ H.1
  exact ⟨(encode_tag t T O G.2.2).trans G.1,
    (encode_tag _ (by rw [J.1]; decide) J.2.1 J.2.2).trans J.1⟩

theorem packet_class {c : Nat} (x : BitVec (W c)) :
    (observe x=.E ↔ (packet (c:=c) x).tag=0) ∧
    (observe x=.T ↔ (packet (c:=c) x).tag=1) ∧
    (observe x=.F ↔ (packet (c:=c) x).tag=2) ∧
    (observe x=.D ↔ (packet (c:=c) x).tag=3) := by
  have B := (decoded_small (wire (c:=c) x)).1
  have S : (packet (c:=c) x).tag=0 ∨ (packet (c:=c) x).tag=1 ∨
      (packet (c:=c) x).tag=2 ∨ (packet (c:=c) x).tag=3 := by
    change (packet (c:=c) x).tag<4 at B
    omega
  rcases S with H|H|H|H <;> simp [observe,H,tagOf]

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact Patch.hold _ _ _ (by simp [Patch.empty])

private def normal {c : Nat} (t : Token) : Patch (W c) :=
  if t.fault then tokenPatch c t else .empty _

private def base {c : Nat} (h : Bool) (t : Token) : Patch (W c) :=
  (if h then .empty _ else control c 1 0 0).compose (normal t)

private theorem control_keeps_wire {c : Nat} (x : BitVec (W c)) :
    wire (c:=c) ((control c 1 0 0).apply x)=wire (c:=c) x := by
  unfold wire WidthByteRows.control put
  rw [Field.read_other_assign _ _ _ _ (.inl (by change (16:Nat)≤16; exact Nat.le_refl _))]

private theorem wire_patch {c : Nat} (y : BitVec (W c)) (t : Token) :
    wire (c:=c) ((tokenPatch c t).apply y)=encode t := by
  unfold wire tokenPatch
  exact Field.read_assign _ _ _

theorem observe_eq_of_wire {c : Nat} {x y : BitVec (W c)}
    (P : wire (c:=c) x=wire (c:=c) y) : observe x=observe y :=
  congrArg (fun v => tagOf (decode v).tag) P

private theorem observe_write {c : Nat} {x : BitVec (W c)} {t : Token}
    (A : wire (c:=c) x=encode t) :
    observe x=tagOf (decode (encode t)).tag :=
  congrArg (fun v => tagOf (decode v).tag) A

private theorem base_keeps_tag {c : Nat} (h : Bool) (x : BitVec (W c)) :
    observe ((base h (packet (c:=c) x)).apply x)=observe x := by
  unfold base normal
  rw [Patch.compose_apply]
  cases h <;> simp only [Bool.false_eq_true,if_false,if_true,empty_apply]
  all_goals
    split
    · exact (observe_write (wire_patch _ _)).trans (congrArg tagOf (packet_transport x))
    · rw [empty_apply] <;>
        exact observe_eq_of_wire (control_keeps_wire x)

private theorem row_view {c : Nat} (r : Nat) (h j : Bool) (u v : BitVec (W c)) :
    row (c:=c) r (h,j) (u,v) =
    let f := packet (c:=c) u
    let d := packet (c:=c) v
    let a := base h f
    let b := base j d
    let y :=
      if f.tag==2 then
        let (eff,t) := departing r (offset h u) u f
        let a := a.compose eff
        if j then (a.compose (tokenPatch c (finish t)),b)
        else (a.compose (tokenPatch c trailToken),b.compose (tokenPatch c t))
      else if j && f.tag==1 then (a.compose (tokenPatch c emptyToken),b)
      else if !j && d.tag==3 then (a.compose (tokenPatch c d),b.compose (tokenPatch c emptyToken))
      else if !j && f.tag==1 && d.tag==0 then (a.compose (tokenPatch c emptyToken),b)
      else (a,b)
    (y.1,if j then y.2.compose (doorPatch v d) else y.2) := rfl

/-- No routing line: old canonical fault may be materialized but each
observed tag is untouched, independently of both old work payloads. -/
theorem inside_default {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c))
    (F : (packet (c:=c) u).tag≠2) (D : (packet (c:=c) v).tag≠3)
    (C : ¬((packet (c:=c) u).tag=1 ∧ (packet (c:=c) v).tag=0)) :
    let q := row (c:=c) r (h,false) (u,v)
    observe (q.1.apply u)=observe u ∧ observe (q.2.apply v)=observe v := by
  have Q : row (c:=c) r (h,false) (u,v)=
      (base h (packet (c:=c) u),base false (packet (c:=c) v)) := by
    simp [row_view,F,D,C]
  rw [Q]
  exact ⟨base_keeps_tag h u,base_keeps_tag false v⟩

private theorem terminal_default {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c))
    (F : (packet (c:=c) u).tag≠2) (T : (packet (c:=c) u).tag≠1) :
    observe (((row (c:=c) r (h,true) (u,v)).1).apply u)=observe u := by
  have Q : (row (c:=c) r (h,true) (u,v)).1=base h (packet (c:=c) u) := by
    simp [row_view,F,T]
  rw [Q]
  exact base_keeps_tag h u

private theorem trail_right_default {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c))
    (T : (packet (c:=c) u).tag=1) (E : (packet (c:=c) v).tag=0) :
    observe (((row (c:=c) r (h,false) (u,v)).2).apply v)=observe v := by
  have Q : (row (c:=c) r (h,false) (u,v)).2=base false (packet (c:=c) v) := by
    simp [row_view,T,E]
  rw [Q]
  exact base_keeps_tag false v

/-- Full literal tag miter for either left header bit with a nonheader
right endpoint, all old bytes and every opcode including malformed. -/
theorem inside_row {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c)) :
    let q := row (c:=c) r (h,false) (u,v)
    (observe (q.1.apply u),observe (q.2.apply v))=
      WidthWaitDrain.inside (observe u) (observe v) := by
  let q := row (c:=c) r (h,false) (u,v)
  change (observe (q.1.apply u),observe (q.2.apply v))=_
  by_cases F : (packet (c:=c) u).tag=2
  · let t := (departing r (offset (c:=c) h u) u (packet (c:=c) u)).2
    have H := forward_wire r h false u v F
    have D := (depart_transport r (offset (c:=c) h u) u).1
    have U : observe u=.F := (packet_class u).2.2.1.mpr F
    have T : observe (q.1.apply u)=.T := by
      have W : wire (c:=c) (q.1.apply u)=encode trailToken := H.1
      exact (observe_write W).trans (by rw [trail_codec]; rfl)
    have R : observe (q.2.apply v)=.F := by
      have W : wire (c:=c) (q.2.apply v)=encode t := H.2 rfl
      exact (observe_write W).trans (by rw [show (decode (encode t)).tag=2 from D.trans F]; rfl)
    simp [WidthWaitDrain.inside,U,T,R]
  · have FN : observe u≠.F := fun H => F ((packet_class u).2.2.1.mp H)
    by_cases D : (packet (c:=c) v).tag=3
    · have H := reverse_wire r h u v F D
      have V : observe v=.D := (packet_class v).2.2.2.mpr D
      have L : observe (q.1.apply u)=.D := by
        exact (observe_write H.1).trans ((congrArg tagOf (packet_transport v)).trans V)
      have R : observe (q.2.apply v)=.E := (observe_write H.2).trans (by rw [empty_codec]; rfl)
      simp [WidthWaitDrain.inside,FN,V,L,R]
    · have DN : observe v≠.D := fun H => D ((packet_class v).2.2.2.mp H)
      by_cases C : (packet (c:=c) u).tag=1 ∧ (packet (c:=c) v).tag=0
      · have U : observe u=.T := (packet_class u).2.1.mpr C.1
        have V : observe v=.E := (packet_class v).1.mpr C.2
        have L : observe (q.1.apply u)=.E :=
          (observe_write (empty_successor_drains r h u v C.1 C.2)).trans (by rw [empty_codec]; rfl)
        have R : observe (q.2.apply v)=.E := (trail_right_default r h u v C.1 C.2).trans V
        simp [WidthWaitDrain.inside,U,V,L,R]
      · have CN : ¬(observe u=.T ∧ observe v=.E) :=
          fun H => C ⟨(packet_class u).2.1.mp H.1,(packet_class v).1.mp H.2⟩
        have H := inside_default r h u v F D C
        have L : observe (q.1.apply u)=observe u := H.1
        have R : observe (q.2.apply v)=observe v := H.2
        simp [WidthWaitDrain.inside,FN,DN,CN,L,R]

/-- Full literal outgoing seam as seen by its old left chart. The right
controller is on another chart and may do arbitrary work concurrently. -/
theorem outgoing_row {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c)) :
    observe (((row (c:=c) r (h,true) (u,v)).1).apply u) =
      WidthWaitDrain.outgoing (observe u) := by
  let q := row (c:=c) r (h,true) (u,v)
  change observe (q.1.apply u)=_
  by_cases F : (packet (c:=c) u).tag=2
  · have W := (forward_wire r h true u v F).1
    have D := (depart_transport r (offset (c:=c) h u) u).2
    have L : observe (q.1.apply u)=.D :=
      (observe_write W).trans ((congrArg tagOf D).trans rfl)
    have U : observe u=.F := (packet_class u).2.2.1.mpr F
    simp [WidthWaitDrain.outgoing,U,L]
  · have FN : observe u≠.F := fun H => F ((packet_class u).2.2.1.mp H)
    by_cases T : (packet (c:=c) u).tag=1
    · have U : observe u=.T := (packet_class u).2.1.mpr T
      have L : observe (q.1.apply u)=.E :=
        (observe_write (terminal_trail_drains r h u v T)).trans (by rw [empty_codec]; rfl)
      simp [WidthWaitDrain.outgoing,U,L]
    · have TN : observe u≠.T := fun H => T ((packet_class u).2.1.mp H)
      have L : observe (q.1.apply u)=observe u := terminal_default r h u v F T
      simp [WidthWaitDrain.outgoing,FN,TN,L]

/-- The incoming door preserves the tag whenever it remains in a
valid WAIT under the F/T hold case. Fault materialization is harmless. -/
theorem incoming_wait_tag {c : Nat} (r : Nat) (h : Bool) (u v : BitVec (W c))
    (P : phase (c:=c) v=2) (O : opcode (c:=c) v≤5)
    (T : observe v=.T ∨ observe v=.F) :
    observe (((row (c:=c) r (h,true) (u,v)).2).apply v)=observe v := by
  have Z : (packet (c:=c) v).tag=1 ∨ (packet (c:=c) v).tag=2 :=
    T.elim (fun H=>Or.inl ((packet_class v).2.1.mp H))
      (fun H=>Or.inr ((packet_class v).2.2.1.mp H))
  rw [wait_ft_row r h u v P O Z]
  split
  · exact (observe_write (wire_patch _ _)).trans (congrArg tagOf (packet_transport v))
  · rfl

#print axioms encode_tag
#print axioms inside_default
#print axioms inside_row
#print axioms outgoing_row
#print axioms incoming_wait_tag
#print axioms observe_eq_of_wire
#print axioms packet_class
end L4.WidthWaitLiteralTags
