import Leader.L4.ReportOwnerReverseShape

/-! A ready nonterminal report command moves its structural F occurrence
on the raw joined mark, regardless of fault, and leaves canonical T. -/
namespace L4.ReportOwnerForwardLocations
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportPrelaunchK1Geometry ReportOwnerResetDrain ReportByteRows
open ReportOwnerProvenanceTransport

variable {s n : Nat} {h : Fin n→Bool}

theorem ready_locations (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L) (R : readyAt d C x i=true) :
    let y := rawNext s x (out C i)
    tok d C y i=MISByteCodec.T ∧ (tok d C y (i+1)).tag=2 := by
  dsimp only
  have W := raw_pair_wire d C x N mask i
  constructor
  · rw [tok_wire,(ready_joined d C x N mask i I R).1,drain_decode_T]
  · rw [tok_wire,W.2]
    exact rank_hop_tag (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
      (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I) R _

end L4.ReportOwnerForwardLocations

namespace L4.ReportOwnerForwardLocations
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportPrelaunchK1Geometry ReportOwnerResetDrain ReportByteRows
open ReportOwnerProvenanceTransport
variable {s n : Nat} {h : Fin n→Bool}

theorem parked_internal_tags
    (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (i : Nat) (I : i+1<C.L)
    (P : (tok d C x i).tag=2) (R : readyAt d C x i=false) :
    let y := rawNext s x (out C i)
    (tok d C y i).tag=(tok d C x i).tag ∧
    (tok d C y (i+1)).tag=(tok d C x (i+1)).tag := by
  let e := out C i
  let y := rawNext s x e
  let p := params d s
  let j := C.route.port i
  let k := C.route.port (i+1)
  let u := bytesL d x e
  let v := bytesR d x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have Row := raw_pair_wire d C x N (CF.mask x X) i
  rw [predecessor_projection] at P
  have EL := rank_idle_left p (h e) (h (rightNeighbor e)) u v j R (.inl P)
  have ER := rank_idle_right p (h e) (h (rightNeighbor e)) u v j k
    (internal_dest C i I) R (.inl P)
  constructor
  · rw [tok_wire,gate_frame d C hh G x y X Y i (by omega),Row.1,workL,EL,tok_wire]
    exact normalize_tag _ _ _ 3 (.inr rfl)
  · rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,Row.2,workR,ER,tok_wire]
    simp only [chartGate,wire]
    exact normalize_tag _ _ _ 2 (.inl rfl)

theorem parked_end_tag
    (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (i : Nat) (I : i<C.L)
    (P : (tok d C x i).tag=2) (R : readyAt d C x i=false) :
    (tok d C (rawNext s x (out C i)) i).tag=(tok d C x i).tag := by
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have Row := raw_pair_wire d C x N (CF.mask x X) i
  rw [predecessor_projection] at P
  have E := rank_idle_left (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ R (.inl P)
  rw [tok_wire,gate_frame d C hh G x y X Y i I,Row.1,workL,E,tok_wire]
  exact normalize_tag _ _ _ 3 (.inr rfl)

theorem ready_turn_tag (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1=C.L) (R : readyAt d C x i=true) :
    (tok d C (rawNext s x (out C i)) i).tag=3 := by
  have W := raw_pair_wire d C x N mask i
  rw [tok_wire,W.1]
  exact rank_turn_tag (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ (end_dest C i I) R _

end L4.ReportOwnerForwardLocations

namespace L4.ReportOwnerForwardLocations
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport
variable {s n : Nat} {h : Fin n→Bool}

def frontTag (k i : Nat) : Nat := if i<k then 1 else if i=k then 2 else 0

def Forward (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  k<C.L ∧ ∀ i,i<C.L→(tok d C x i).tag=frontTag k i

private theorem nonreply (k i : Nat) : frontTag k i≠3 := by
  unfold frontTag
  split
  · decide
  · split <;> decide

private theorem not_front {k i : Nat} (H : i≠k) : frontTag k i≠2 := by
  unfold frontTag
  simp only [H,if_false]
  split <;> decide

private theorem no_clear (k j : Nat) :
    ¬(frontTag k j=1 ∧ frontTag k (j+1)=0) := by
  rintro ⟨A,B⟩
  have I : j<k := by
    by_cases E : j<k
    · exact E
    · simp [frontTag,E] at A
      split at A <;> contradiction
  by_cases D : j+1=k
  · simp [frontTag,D] at B
  · have E : j+1<k := by omega
    simp [frontTag,E] at B

private theorem unaffected {i k : Nat} (A : i≠k) (B : i≠k+1) :
    frontTag k i=frontTag (k+1) i := by
  have C : i<k ↔ i<k+1 := by omega
  simp only [frontTag,C,A,B,if_false]

private theorem same_trail {k i : Nat} (H : i≠k) :
    frontTag k i=ReportOwnerReverseShape.backTag k i := by
  simp [frontTag,ReportOwnerReverseShape.backTag,H]

/-- The raw non-door mark preserves the single F cursor, advances it by
one chart occurrence, or turns it into the single reverse D cursor at
the terminal cut. This is shape only, not command payload provenance. -/
theorem non_door_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : Forward d C x k)
    (e : Fin n) (D0 : e≠door C) :
    let y := rawNext s x e
    Forward d C y k ∨
      (e=out C k ∧
        (Forward d C y (k+1) ∨
          (k+1=C.L ∧ ReportOwnerReverseShape.Reverse d C y k))) := by
  dsimp only
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x e X
  by_cases A : ∃ j,j<C.L ∧ e=out C j
  · obtain ⟨j,J,rfl⟩ := A
    have local_frame (i : Nat) (I : i<C.L) (E : i≠j) (F0 : i≠j+1) :
        tok d C (rawNext s x (out C j)) i=tok d C x i :=
      decoded_frame d C hh G x _ X Y i I (raw_link_frame d C x j i J I E F0)
    by_cases V : j+1<C.L
    · by_cases K : j=k
      · subst j
        cases RD : readyAt d C x k
        · left
          have H : (tok d C x k).tag=2 := by simpa [frontTag] using R.2 k J
          have ⟨P,S⟩ := parked_internal_tags d C hh G F N x X k V H RD
          refine ⟨R.1,?_⟩
          intro i I
          by_cases E : i=k
          · subst i; exact P.trans (R.2 _ J)
          · by_cases H0 : i=k+1
            · subst i; exact S.trans (R.2 _ V)
            · rw [local_frame i I E H0,R.2 i I]
        · right
          refine ⟨rfl,.inl ⟨V,?_⟩⟩
          obtain ⟨P,S⟩ := ready_locations d C x N (CF.mask x X) k V RD
          intro i I
          by_cases E : i=k
          · subst i; rw [P]; simp [frontTag,MISByteCodec.T]
          · by_cases H0 : i=k+1
            · subst i; simpa [frontTag] using S
            · rw [local_frame i I E H0,R.2 i I,unaffected E H0]
      · left
        have LF : (tok d C x j).tag≠2 := (R.2 j J) ▸ not_front K
        have NR : (tok d C x (j+1)).tag≠3 := (R.2 (j+1) V) ▸ nonreply k (j+1)
        have NC : ¬((tok d C x j).tag=1 ∧ (tok d C x (j+1)).tag=0) := by
          rw [R.2 j J,R.2 (j+1) V]
          exact no_clear k j
        obtain ⟨P,S⟩ := idle_internal_tags d C hh G F N x X j V LF NR NC
        refine ⟨R.1,?_⟩
        intro i I
        by_cases E : i=j
        · subst i; exact P.trans (R.2 _ J)
        · by_cases H0 : i=j+1
          · subst i; exact S.trans (R.2 _ V)
          · rw [local_frame i I E H0,R.2 i I]
    · have E0 : j+1=C.L := by omega
      by_cases K : j=k
      · subst j
        cases RD : readyAt d C x k
        · left
          have H : (tok d C x k).tag=2 := by simpa [frontTag] using R.2 k J
          have P := parked_end_tag d C hh G F N x X k J H RD
          refine ⟨R.1,?_⟩
          intro i I
          by_cases E : i=k
          · subst i; exact P.trans (R.2 _ J)
          · rw [local_frame i I E (by omega),R.2 i I]
        · right
          refine ⟨rfl,.inr ⟨E0,J,?_⟩⟩
          have P := ready_turn_tag d C x N (CF.mask x X) k E0 RD
          intro i I
          by_cases E : i=k
          · subst i; simpa [ReportOwnerReverseShape.backTag] using P
          · rw [local_frame i I E (by omega),R.2 i I,same_trail E]
      · left
        have LF : (tok d C x j).tag≠2 := (R.2 j J) ▸ not_front K
        have LT : (tok d C x j).tag≠1 := by
          rw [R.2 j J]
          have NK : ¬j<k := by have B := R.1; omega
          simp [frontTag,NK,K]
        have P := idle_end_tag d C hh G F N x X j E0 LF LT
        refine ⟨R.1,?_⟩
        intro i I
        by_cases E : i=j
        · subst i; exact P.trans (R.2 _ J)
        · rw [local_frame i I E (by omega),R.2 i I]
  · left
    refine ⟨R.1,?_⟩
    intro i I
    have W := raw_off_frame d C x e D0 (fun j J H=>A ⟨j,J,H⟩) i I
    rw [decoded_frame d C hh G x y X Y i I W,R.2 i I]

end L4.ReportOwnerForwardLocations
