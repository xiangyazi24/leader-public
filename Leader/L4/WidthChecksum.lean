import Leader.L4.WidthByteRows

namespace L4.WidthChecksum
open AllSizeProtocol WidthByteRows

/-- Literal one-bit OUT projection of the padded width sheet. -/
def output {c : Nat} (x : BitVec (W c)) : Nat := WidthByteRows.get (c:=c) x 6 1 (by decide)

/-- The low-order counter digit presented to the checksum tour. -/
def counter {c : Nat} (x : BitVec (W c)) : Nat := WidthByteRows.get (c:=c) x 5 1 (by decide)

def packet {c : Nat} (x : BitVec (W c)) : Token :=
  decode ((suffixField c 14 16 (by decide)).read x)

private theorem fit_counter {c : Nat} (x : BitVec (W c)) : counter (c:=c) x<2 :=
  ((suffixField c 5 1 (by decide)).read x).isLt

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact Patch.hold _ _ _ (by simp [Patch.empty])

private def srcReset (c : Nat) (h : Bool) : Patch (W c) :=
  if h then .empty _ else control c 1 0 0

private theorem keep_high {c j : Nat} (x : BitVec (W c)) (H : j+1≤7) (v : Nat) :
    WidthByteRows.get (c:=c) ((control c 1 0 v).apply x) j 1 (by omega) =
      WidthByteRows.get (c:=c) x j 1 (by omega) := by
  unfold WidthByteRows.get WidthByteRows.control put
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]; omega))]

private theorem keep_reset {c j : Nat} (h : Bool) (x : BitVec (W c)) (H : j+1≤7) :
    WidthByteRows.get (c:=c) ((srcReset c h).apply x) j 1 (by omega)=WidthByteRows.get (c:=c) x j 1 (by omega) := by
  cases h
  · exact keep_high x H 0
  · simp [srcReset,empty_apply]

private theorem keep_token {c j : Nat} (x : BitVec (W c)) (H : j+1≤7) (t : Token) :
    WidthByteRows.get (c:=c) ((tokenPatch c t).apply x) j 1 (by omega)=WidthByteRows.get (c:=c) x j 1 (by omega) := by
  unfold WidthByteRows.get tokenPatch
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]; omega))]

private theorem keep_output {c j : Nat} (x : BitVec (W c)) (H : j+1≤6) (v : Nat) :
    WidthByteRows.get (c:=c) ((put c 6 1 (by decide) v).apply x) j 1 (by omega)=
      WidthByteRows.get (c:=c) x j 1 (by omega) := by
  unfold WidthByteRows.get put
  rw [Field.read_other_assign _ _ _ _ (.inr (by simp [suffixField]; omega))]

private theorem write_output {c : Nat} (x : BitVec (W c)) (v : Nat) (L : v<2) :
    output (c:=c) ((put c 6 1 (by decide) v).apply x)=v := by
  unfold output WidthByteRows.get put
  rw [Field.read_assign,BitVec.toNat_ofNat,Nat.mod_eq_of_lt L]

/-- The full old-pair row, not merely the outgoing client effect, writes
OUT from the **old** counter digit and clipped offset on a real healthy
F5 departure; neither the controller prepatch nor token routing can
change IN, LAST or the counter. No premise on the old right token. -/
theorem raw_checksum_step {c : Nat} (r : Nat) (hu hv : Bool) (u v : BitVec (W c))
    (F : packet (c:=c) u={tag:=2,op:=5}) :
    let y := (row (c:=c) r (hu,hv) (u,v)).1.apply u
    output (c:=c) y=(if offset (c:=c) hu u<c then counter (c:=c) u else 0) ∧
      inside (c:=c) y=inside (c:=c) u ∧ last (c:=c) y=last (c:=c) u ∧
      counter (c:=c) y=counter (c:=c) u := by
  let z := if offset (c:=c) hu u<c then counter (c:=c) u else 0
  let q := srcReset c hu
  let t := if hv then finish {tag:=2,op:=5} else trailToken
  have L : z<2 := by unfold z; split; exact fit_counter u; decide
  have D : (row (c:=c) r (hu,hv) (u,v)).1.apply u =
      (tokenPatch c t).apply ((put c 6 1 (by decide) z).apply (q.apply u)) := by
    change decode ((suffixField c 14 16 (by decide)).read u) = _ at F
    cases hv <;>
      simp [row,F,departing,Patch.compose_apply,q,srcReset,z,counter,t,empty_apply]
  dsimp only
  rw [D]
  have keep (j : Nat) (J : j+1≤6) :
      WidthByteRows.get (c:=c) ((tokenPatch c t).apply ((put c 6 1 (by decide) z).apply (q.apply u)))
        j 1 (by omega)= WidthByteRows.get (c:=c) u j 1 (by omega) := by
    rw [keep_token _ (by omega) t,keep_output _ J,keep_reset hu _ (by omega)]
  refine ⟨?_,?_,?_,keep 5 (by decide)⟩
  · unfold output
    rw [keep_token _ (by decide) t]
    exact write_output _ z L
  · unfold inside
    rw [keep 3 (by decide)]
  · unfold last
    rw [keep 4 (by decide)]

#print axioms raw_checksum_step

/-- Inherited canonical F-faults are genuine moving packets, not stuck
debris: a terminal edge yields D-fault; an interior edge writes T/F. -/
theorem raw_fault_motion {c : Nat} (r : Nat) (hu hv : Bool) (u v : BitVec (W c))
    (F : packet (c:=c) u=faultCode 2) :
    let q := row (c:=c) r (hu,hv) (u,v)
    ((suffixField c 14 16 (by decide)).read (q.1.apply u))=
      encode (if hv then faultCode 3 else trailToken) ∧
      (hv=false → ((suffixField c 14 16 (by decide)).read (q.2.apply v))=
        encode (faultCode 2)) := by
  change decode ((suffixField c 14 16 (by decide)).read u) = _ at F
  dsimp only
  cases hv
  · simp [row,F,departing,faultCode,Patch.compose_apply,tokenPatch,Field.read_assign]
  · simp [row,F,departing,faultCode,finish,Patch.compose_apply,tokenPatch,Field.read_assign]

#print axioms raw_fault_motion
end L4.WidthChecksum
