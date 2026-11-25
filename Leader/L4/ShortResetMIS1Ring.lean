import Leader.L4.ShortResetRow
import Leader.L4.PhysicalCustody

namespace L4.ShortResetMIS1Ring
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow PhysicalCustody
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private theorem geometry_frames (h : Pair Bool) (x : Pair (BitVec 96))
    (p : Pair (Patch 96)) (j : Fin 3) :
    (kField j).read (patchPair (ShortGeo.mis.patches 3 h x p) x).1 =
      (kField j).read (patchPair p x).1 ∧
    (kField j).read (patchPair (ShortGeo.mis.patches 3 h x p) x).2 =
      (kField j).read (patchPair p x).2 := by
  have H (i : Fin 19) : ¬ ShortGeo.mis.owned ((kField j).offset+i.val) := by
    intro E
    have K := E.1
    change 93≤19*(2-j.val)+i.val at K
    have := i.isLt
    omega
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h x p _ (H ⟨i,hi⟩)).1
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h x p _ (H ⟨i,hi⟩)).2

def header {s n : Nat} (x : Raw s n) (i : Fin n) : Bool :=
  (oldHeaders (rows s) (x i)).h1

def pairIn {s n : Nat} (x : Raw s n) (e : Fin n) : Pair (BitVec 96) :=
  ((x e).mis1,(x (rightNeighbor e)).mis1)

def pairHeader {s n : Nat} (x : Raw s n) (e : Fin n) : Pair Bool :=
  (header x e,header x (rightNeighbor e))

private theorem joined_mis1 {a : LargeParams} (b : LargeRows a) (x : Pair (LargeSite a)) :
    let h := Pair.map (fun t => (oldHeaders b t).h1) x
    let m := Pair.map LargeSite.mis1 x
    Pair.map LargeSite.mis1 (largePair b x) =
      patchPair (ShortGeo.mis.patches 3 h m (b.mis h m)) m := by
  rcases x with ⟨u,v⟩
  rfl

/-- The actual joined pair's MIS1 token fields agree with the immutable-old
MIS1 work row; geometry updates only its disjoint three high bits. -/
theorem work_to_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) :
    let q := patchPair (MISByteRows.row (pairHeader x e) (pairIn x e)) (pairIn x e)
    (kField j).read (rawNext s x e e).mis1 = (kField j).read q.1 ∧
      (kField j).read (rawNext s x e (rightNeighbor e)).mis1=(kField j).read q.2 := by
  let h := pairHeader x e
  let old := pairIn x e
  have H := geometry_frames h old (BStarShort.shortMIS h old) j
  have G : (kField j).read ((BStarShort.shortMIS h old).1.apply old.1) =
      (kField j).read ((MISByteRows.row h old).1.apply old.1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    apply BStarShort.mis_apply_outside
    left
    change 19*(2-j.val)+i<89
    omega
  dsimp only
  constructor
  · rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
      simp [rawNext,AllSizeS1Geometry.step]]
    have F := congrArg (fun z : Pair (BitVec 96) => (kField j).read z.1)
      (joined_mis1 (rows s) (x e,x (rightNeighbor e)))
    exact F.trans (H.1.trans G)
  · rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
      simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
    exact H.2

theorem reset_out_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3) (dst : destination (header x (rightNeighbor e)) j=some k)
    (front : oldK (header x e) (x e).mis1 j=resetForward) :
    (kField j).read (rawNext s x e e).mis1=encode T ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode resetForward := by
  have H := reset_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst front
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩

theorem reset_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) (dst : destination (header x (rightNeighbor e)) j=none)
    (front : oldK (header x e) (x e).mis1 j=resetForward) :
    (kField j).read (rawNext s x e e).mis1=encode resetReply := by
  exact (work_to_raw x e sep j).1.trans
    (reset_turn_pair _ _ _ _ _ dst front)

theorem reset_back_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3) (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (back : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=resetReply) :
    (kField j).read (rawNext s x e e).mis1=encode resetReply ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode E := by
  have H := reset_back_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst trail back
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩

/-- Actual inbound mark creates RESET0 from a header in ISSUE0. -/
theorem reset_issue_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=1)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode resetForward := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (reset_issue_pair _ _ _ phase op)

/-- Actual inbound mark consumes the authenticated RESET0 root reply. -/
theorem reset_consume_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0)
    (reply : oldK true (x (rightNeighbor e)).mis1 0=resetReply) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode E := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (reset_consume_pair _ _ _ phase op reply)

/-- Any inbound mark with the old predecessor trail leaves the
tracked forward or trail lane unchanged in the full raw ring. -/
theorem reset_inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=resetForward ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 := by
  exact (work_to_raw x e sep k).2.trans (reset_inbound_frame_pair _ _ _ _ _ _ dst trail safe)

private theorem work_to_raw_right_controller {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) {k : Nat} (f : Field 96 k) (bound : f.offset+k≤93) :
    let z := ((MISByteRows.row (pairHeader x e) (pairIn x e)).2).apply (pairIn x e).2
    f.read (rawNext s x e (rightNeighbor e)).mis1=f.read z := by
  let h := pairHeader x e
  let old := pairIn x e
  have G : f.read (patchPair (ShortGeo.mis.patches 3 h old (BStarShort.shortMIS h old)) old).2
      = f.read (patchPair (BStarShort.shortMIS h old) old).2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ho : ¬ShortGeo.mis.owned (f.offset+i) := by
      intro E
      have le := E.1
      change 93≤f.offset+i at le
      omega
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h old (BStarShort.shortMIS h old) _ ho).2
  dsimp only
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
    simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  exact G

/-- True on the actual raw edge and old H2 header geometry: issuance
writes WAIT0, not merely a forward-token bit pattern. -/
theorem reset_issue_controller_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=1)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    get y 81 2 (by decide)=2 ∧ get y 78 3 (by decide)=0 := by
  have A := work_to_raw_right_controller x e sep (lane 81 2 (by decide)) (by decide)
  have B := work_to_raw_right_controller x e sep (lane 78 3 (by decide)) (by decide)
  simp only [pairHeader,head] at A B
  have H := reset_issue_controller_pair (header x e) (x e).mis1
    (x (rightNeighbor e)).mis1 phase op
  exact ⟨(congrArg BitVec.toNat A).trans H.1,(congrArg BitVec.toNat B).trans H.2⟩

/-- True on the actual inbound raw edge: the genuine RESET0 receipt
clears K0 (separate theorem) and advances to ISSUE1. -/
theorem reset_consume_controller_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0)
    (reply : oldK true (x (rightNeighbor e)).mis1 0=resetReply) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    get y 81 2 (by decide)=1 ∧ get y 78 3 (by decide)=1 := by
  have A := work_to_raw_right_controller x e sep (lane 81 2 (by decide)) (by decide)
  have B := work_to_raw_right_controller x e sep (lane 78 3 (by decide)) (by decide)
  simp only [pairHeader,head] at A B
  have H := reset_consume_controller_pair (header x e) (x e).mis1
    (x (rightNeighbor e)).mis1 phase op reply
  exact ⟨(congrArg BitVec.toNat A).trans H.1,(congrArg BitVec.toNat B).trans H.2⟩

/-- On an actual inbound edge the live root WAIT0/forward-or-trail
lane is stable, including the independent responder-door phase. -/
theorem reset_root_inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0)
    (safe : oldK true (x (rightNeighbor e)).mis1 0=resetForward ∨
      oldK true (x (rightNeighbor e)).mis1 0=T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField 0).read (x (rightNeighbor e)).mis1 := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (reset_root_inbound_frame_pair _ _ _ wait op safe)

/-- Any outgoing edge of a tracked prefix trail that still faces forward
or trail traffic leaves the selected raw lane unchanged. -/
theorem reset_prefix_trail_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=resetForward ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 := by
  exact (work_to_raw x e sep j).1.trans (reset_prefix_trail_frame_pair _ _ _ _ _ _ dst trail safe)

/-- A raw mark not touching the tracked site cannot change any MIS1 byte. -/
theorem reset_remote_frame_raw {s n : Nat} (x : Raw s n) (e i : Fin n)
    (left : i≠e) (right : i≠rightNeighbor e) :
    (rawNext s x e i).mis1=(x i).mis1 := by
  simp [rawNext,AllSizeS1Geometry.step,left,right]

/-- Actual MIS1 outgoing edge cannot change a returning RESET0 reply or
a clear suffix lane facing a clear successor (or the terminal turn). -/
theorem reset_reverse_outbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (safe : oldK (header x e) (x e).mis1 j=resetReply ∨
      oldK (header x e) (x e).mis1 j=E)
    (dst : destination (header x (rightNeighbor e)) j=none ∨
      ∃ k, destination (header x (rightNeighbor e)) j=some k ∧
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 := by
  exact (work_to_raw x e sep j).1.trans (reset_reverse_outbound_frame_pair
    _ _ _ _ _ safe.symm (by
      intro k hk
      rcases dst with D | ⟨j,D,E⟩
      · simp [D] at hk
      · have K : j=k := Option.some.inj (D.symm.trans hk)
        simpa only [←K] using E))

/-- Actual MIS1 incoming edge holds the cleared suffix when its
predecessor is that suffix or the returning RESET0 frontier. -/
theorem reset_reverse_inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (safe : oldK (header x e) (x e).mis1 j=resetReply ∨
      oldK (header x e) (x e).mis1 j=E)
    (clear : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 := by
  exact (work_to_raw x e sep k).2.trans (reset_reverse_inbound_frame_pair
    _ _ _ _ _ _ dst safe.symm clear)

private theorem work_to_raw_left_controller {s n : Nat} (x : Raw s n) (e : Fin n)
    {k : Nat} (f : Field 96 k) (bound : f.offset+k≤83) :
    let z := ((MISByteRows.row (pairHeader x e) (pairIn x e)).1).apply (pairIn x e).1
    f.read (rawNext s x e e).mis1=f.read z := by
  let h := pairHeader x e
  let old := pairIn x e
  have G : f.read (patchPair (ShortGeo.mis.patches 3 h old (BStarShort.shortMIS h old)) old).1
      = f.read (patchPair (BStarShort.shortMIS h old) old).1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ho : ¬ShortGeo.mis.owned (f.offset+i) := by
      intro E
      have le := E.1
      change 93≤f.offset+i at le
      omega
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h old (BStarShort.shortMIS h old) _ ho).1
  have E : f.read (patchPair (BStarShort.shortMIS h old) old).1 =
      f.read (patchPair (MISByteRows.row h old) old).1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact BStarShort.mis_apply_outside h old (f.offset+i) (.inl (by omega))
  dsimp only
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
    simp [rawNext,AllSizeS1Geometry.step]]
  exact G.trans E

/-- The source control of an actual MIS1 header is untouched on its
outgoing mark, independently of its own or its neighbors' lane content. -/
theorem reset_controller_outgoing_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (head : header x e=true) :
    let y := (rawNext s x e e).mis1
    get y 81 2 (by decide)=get (x e).mis1 81 2 (by decide) ∧
    get y 78 3 (by decide)=get (x e).mis1 78 3 (by decide) := by
  let pa : Field 96 2 := lane 81 2 (by decide)
  let pc : Field 96 3 := lane 78 3 (by decide)
  have A := work_to_raw_left_controller x e pa (by decide)
  have B := work_to_raw_left_controller x e pc (by decide)
  simp only [pairHeader,head] at A B
  exact ⟨congrArg BitVec.toNat (A.trans (source_field_outgoing_pair pa
    (by decide) (by decide) _ _ _)), congrArg BitVec.toNat (B.trans
    (source_field_outgoing_pair pc (by decide) (by decide) _ _ _))⟩

/-- A genuine forward/trail root holds WAIT0 on the old incoming mark.
No assumptions on the predecessor's other lanes are needed. -/
theorem reset_controller_inbound_hold_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0)
    (safe : oldK true (x (rightNeighbor e)).mis1 0=resetForward ∨
      oldK true (x (rightNeighbor e)).mis1 0=T) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    get y 81 2 (by decide)=2 ∧ get y 78 3 (by decide)=0 := by
  let v := (x (rightNeighbor e)).mis1
  have tags : (oldK true v 0).tag=1 ∨ (oldK true v 0).tag=2 := by
    rcases safe with S|S
    · exact .inr (by change (oldK true (x (rightNeighbor e)).mis1 0).tag=2; rw [S]; rfl)
    · exact .inl (by change (oldK true (x (rightNeighbor e)).mis1 0).tag=1; rw [S]; rfl)
  have Z : get v 78 3 (by decide)=0 := op
  have H := source_wait_holds v _ wait (by omega) tags
  let pa : Field 96 2 := lane 81 2 (by decide)
  let pc : Field 96 3 := lane 78 3 (by decide)
  have A := work_to_raw_right_controller x e sep pa (by decide)
  have B := work_to_raw_right_controller x e sep pc (by decide)
  simp only [pairHeader,head] at A B
  exact ⟨(congrArg BitVec.toNat (A.trans (source_field_held_inbound_pair pa
    (by decide) (by decide) _ _ _ H))).trans wait,
    (congrArg BitVec.toNat (B.trans (source_field_held_inbound_pair pc
    (by decide) (by decide) _ _ _ H))).trans op⟩

end L4.ShortResetMIS1Ring

namespace L4.ShortResetMIS1Ring
open AllSizeProtocol MISByteCodec PhysicalCustody

theorem selector_right_projection_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) :
    let z := ((MISByteRows.row (pairHeader x e) (pairIn x e)).2).apply (pairIn x e).2
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92=z.getLsbD 92 := by
  have A := work_to_raw_right_controller x e sep (lane 92 1 (by decide)) (by decide)
  have E := congrArg (fun z : BitVec 1=>z.getLsbD 0) A
  simpa [Field.read, BitVec.getLsbD_extractLsb', lane] using E

end L4.ShortResetMIS1Ring
