import Leader.L4.ReportPrelaunchDoorProducer

/-! Exact physical steps of the owner chart. These are transport facts,
not user-controlled source flags or a lease invariant. -/
namespace L4.ReportOwnerProvenanceTransport
open AllSizeProtocol PhysicalCustody
open ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportPrelaunchK1Geometry ReportByteRows

variable {s n : Nat} {h : Fin n→Bool}

def readyAt (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Bool :=
  rankReady (params d s) (h (out C i)) (bytesL d x (out C i)) (C.route.port i)

theorem chart_succ (C : Chart h) (i : Nat) :
    rightNeighbor (out C i)=out C (i+1) :=
  rfl

theorem predecessor_projection (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) :
    ReportOwnerResetDrain.tok d C x i=
    publicationToken (params d s) (h (out C i)) (bytesL d x (out C i)) (C.route.port i) := by
  rw [tok_wire,rankToken_wire]
  rfl

theorem successor_projection (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) :
    ReportOwnerResetDrain.tok d C x (i+1)=
    publicationToken (params d s) (h (rightNeighbor (out C i))) (bytesR d x (out C i))
      (C.route.port (i+1)) := by
  rw [predecessor_projection]
  simp only [bytesL,bytesR,chart_succ]

/-- Ready internal departure writes canonical T at its old slot, and
the destination gets exactly the old router's arrival intent. In
particular there is no credit to a normalized incumbent at the destination. -/
theorem ready_joined (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L) (R : readyAt d C x i=true) :
    let e := out C i
    let y := rawNext s x e
    let p := params d s
    let j := C.route.port i
    let k := C.route.port (i+1)
    let u := bytesL d x e
    let v := bytesR d x e
    wire d C y i=resetTokenWire p MISByteCodec.T ∧
    ∃ t,rankRouteR p (h e) (h (rightNeighbor e)) u v j k=some t ∧
      wire d C y (i+1)=resetTokenWire p t := by
  dsimp only
  have W := raw_pair_wire d C x N mask i
  have L := rank_hop_left (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I) R
  refine ⟨W.1.trans L,?_⟩
  have Q := rank_row_right (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I)
  rw [W.2,workR,Q]
  unfold rankRouteR
  simp only [readyAt] at R
  simp only [R,if_true,Option.elim]
  exact ⟨_,rfl,rfl⟩

/-- An old reply at the successor is transported back with its exact
old decoded token reencoded, not recreated from the new state. Its
successor slot is wiped on that same physical mark. -/
theorem reverse_joined (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L)
    (P : (ReportOwnerResetDrain.tok d C x i).tag≠2)
    (D : (ReportOwnerResetDrain.tok d C x (i+1)).tag=3) :
    let y := rawNext s x (out C i)
    wire d C y i=resetTokenWire (params d s) (ReportOwnerResetDrain.tok d C x (i+1)) ∧
    wire d C y (i+1)=resetTokenWire (params d s) MISByteCodec.E := by
  dsimp only
  rw [predecessor_projection] at P
  rw [successor_projection] at D ⊢
  have W := raw_pair_wire d C x N mask i
  have V := rank_reverse_pair (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I) P D
  exact ⟨W.1.trans V.1,W.2.trans V.2⟩

/-- The reverse mark creates only the predecessor D occurrence:
the final predecessor decoder still sees D, and the old D slot is E. -/
theorem reverse_locations (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L)
    (P : (ReportOwnerResetDrain.tok d C x i).tag≠2)
    (D : (ReportOwnerResetDrain.tok d C x (i+1)).tag=3) :
    let y := rawNext s x (out C i)
    (ReportOwnerResetDrain.tok d C y i).tag=3 ∧
    ReportOwnerResetDrain.tok d C y (i+1)=MISByteCodec.E := by
  dsimp only
  obtain ⟨L,R⟩ := reverse_joined d C x N mask i I P D
  constructor
  · rw [tok_wire,L,tok_wire d C x (i+1),rank_reverse_tag]
    rw [tok_wire] at D
    exact D
  · rw [tok_wire,R,drain_decode_E]

/-- Sibling and external marks that leave an owner wire alone also
leave the decoded occurrence alone, since the cached decode gate is fixed. -/
theorem decoded_frame (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (x y : Raw s n)
    (X : ReportOwnerResetDrain.Cached d hh Q x)
    (Y : ReportOwnerResetDrain.Cached d hh Q y)
    (i : Nat) (I : i<C.L) (H : wire d C y i=wire d C x i) :
    ReportOwnerResetDrain.tok d C y i=ReportOwnerResetDrain.tok d C x i := by
  rw [tok_wire,tok_wire,H,gate_frame d C hh G x y X Y i I]

theorem normalize_tag (p : Params) (g : Bool) (w : BitVec (tokenW p))
    (side : Nat) (S : side=2 ∨ side=3) :
    (decode p g (rankNormWire p side g w)).tag=(decode p g w).tag := by
  rcases rank_norm_cases p g w side S with E|⟨_,T,_,T',_,_⟩
  · exact congrArg MISByteCodec.Token.tag E
  · exact T'.trans T.symm

private theorem not_ready_of_nonfront (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (H : (ReportOwnerResetDrain.tok d C x i).tag≠2) :
    readyAt d C x i=false := by
  rw [predecessor_projection] at H
  apply Bool.eq_false_iff.mpr
  intro R
  exact H ((rankReady_iff _ _ _ _).mp R).1

theorem idle_internal_tags
    (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : ReportOwnerResetDrain.Cached d hh Q x)
    (i : Nat) (I : i+1<C.L)
    (P : (ReportOwnerResetDrain.tok d C x i).tag≠2)
    (D : (ReportOwnerResetDrain.tok d C x (i+1)).tag≠3)
    (T : ¬((ReportOwnerResetDrain.tok d C x i).tag=1 ∧
      (ReportOwnerResetDrain.tok d C x (i+1)).tag=0)) :
    let y := rawNext s x (out C i)
    (ReportOwnerResetDrain.tok d C y i).tag=(ReportOwnerResetDrain.tok d C x i).tag ∧
    (ReportOwnerResetDrain.tok d C y (i+1)).tag=(ReportOwnerResetDrain.tok d C x (i+1)).tag := by
  dsimp only
  let e := out C i
  let y := rawNext s x e
  let p := params d s
  let j := C.route.port i
  let k := C.route.port (i+1)
  let u := bytesL d x e
  let v := bytesR d x e
  have CF := ReportOwnerResetDrain.cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have Row := raw_pair_wire d C x N (CF.mask x X) i
  have NR := not_ready_of_nonfront d C x i P
  have W := internal_dest C i I
  have P' := P
  have D' := D
  have T' := T
  rw [predecessor_projection] at P'
  rw [successor_projection] at D'
  rw [predecessor_projection,successor_projection] at T'
  have EL := rank_idle_left p (h e) (h (rightNeighbor e)) u v j NR
    (.inr ⟨P',by rw [W]; exact ⟨D',T'⟩⟩)
  have ER := rank_idle_right p (h e) (h (rightNeighbor e)) u v j k W NR (.inr D')
  constructor
  · rw [tok_wire,gate_frame d C hh G x y X Y i (by omega),Row.1,workL,EL,tok_wire]
    exact normalize_tag _ _ _ 3 (.inr rfl)
  · rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,Row.2,workR,ER,tok_wire]
    simp only [chartGate,wire]
    exact normalize_tag _ _ _ 2 (.inl rfl)

theorem idle_end_tag
    (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : ReportOwnerResetDrain.Cached d hh Q x)
    (i : Nat) (I : i+1=C.L)
    (P : (ReportOwnerResetDrain.tok d C x i).tag≠2)
    (T : (ReportOwnerResetDrain.tok d C x i).tag≠1) :
    (ReportOwnerResetDrain.tok d C (rawNext s x (out C i)) i).tag=
      (ReportOwnerResetDrain.tok d C x i).tag := by
  let e := out C i
  let y := rawNext s x e
  have CF := ReportOwnerResetDrain.cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have Row := raw_pair_wire d C x N (CF.mask x X) i
  have NR := not_ready_of_nonfront d C x i P
  have Z := end_dest C i I
  rw [predecessor_projection] at P T
  have E := rank_idle_left (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ NR
    (.inr ⟨P,by rw [Z]; exact T⟩)
  rw [tok_wire,gate_frame d C hh G x y X Y i (by omega),Row.1,workL,E,tok_wire]
  exact normalize_tag _ _ _ 3 (.inr rfl)

end L4.ReportOwnerProvenanceTransport
