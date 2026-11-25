import Leader.L4.BStarPublic
import Leader.L4.TaggedGeometry

namespace L4.BStarPublicFrame
open AllSizeProtocol BStarPublicCodec BStarPublic

def full {w k : Nat} (f : Field w k) (m : BitVec w) (b : Bool) : Prop :=
  ∀ j, j<k → m.getLsbD (f.offset+j)=b

theorem read_patch_hold {w k} (f : Field w k) (p : Patch w) (raw : BitVec w)
    (h : full f p.mask false) : f.read (p.apply raw)=f.read raw := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Field.read,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  exact p.hold raw (f.offset+j) (h j hj)

theorem read_patch_write {w k} (f : Field w k) (p : Patch w) (raw : BitVec w)
    (h : full f p.mask true) : f.read (p.apply raw)=f.read p.value := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Field.read,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  exact p.write raw (f.offset+j) (h j hj)

/-- This form deliberately preserves a held spare raw code rather
than assuming every old field was canonically packed. -/
theorem decoded_field {w k} {V : Type} (read : BitVec k → V)
    (f : Field w k) (p : Patch w) (raw : BitVec w) (y : V)
    (hw : read (f.read p.value)=y)
    (h : full f p.mask true ∨ (full f p.mask false ∧ read (f.read raw)=y)) :
    read (f.read (p.apply raw))=y := by
  rcases h with h|⟨h,hv⟩
  · rwa [read_patch_write f p raw h]
  · rwa [read_patch_hold f p raw h]

/-- The public mask's arithmetic lane agrees with the Field
interval, including the zero-width residue case p=1. -/
theorem lane_support {w k} (f : Field w k) (i : Nat) :
    (BitVec.ofNat w ((2^k-1)*2^f.offset)).getLsbD i=true ↔
      f.offset≤i ∧ i<f.offset+k := by
  have h : BitVec.ofNat w ((2^k-1)*2^f.offset)=(f.assign 0).mask := by
    apply BitVec.eq_of_toNat_eq
    unfold Field.assign
    rw [BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth_of_le (by have := f.fits; omega),
      BitVec.toNat_allOnes,Nat.shiftLeft_eq]
  rw [h,Field.inMask]

private theorem left_source {p c : Nat} (u v : Site p c) : (pairStep u v).1.source=u.source := by
  have hm : (materialize u v).source=u.source := by unfold materialize; split <;> rfl
  have hf (a : Site p c) : (fireInitiator a).source=a.source := by unfold fireInitiator; split <;> rfl
  have hi (a b : Site p c) : (impact a b).1.source=a.source := by unfold impact; split <;> rfl
  have hb (g : Bool) (a b : Site p c) : (followerBullet g a b).1.source=a.source := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  have hp (a b : Site p c) : (payment a b).1.source=a.source := by
    unfold payment
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  have hN : (native (materialize u v) v).1.source=u.source := by
    simp only [native,hb,hi,hf,hm]
  have hPre : (stepPrefix u v).1.source=u.source := by
    simp only [stepPrefix,hp,hN]
  unfold pairStep
  generalize stepPrefix u v = pp at hPre ⊢
  rcases pp with ⟨a,b⟩
  have hB (flag : Bool) (a b : Site p c) :
      (finishBirth flag a b).1.source=a.source := by
    unfold finishBirth
    split <;> rfl
  exact (hB _ _ _).trans hPre

/-- Independently, the literal pair never modifies the initiator's
residue, leader flag, or source field. -/
theorem left_static {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.residue=u.residue ∧ (pairStep u v).1.leader=u.leader ∧
      (pairStep u v).1.source=u.source :=
  ⟨(pair_geometric_fields u v).1,(pair_geometric_fields u v).2.1,left_source u v⟩

/-- N5 issues left signal on every edge, independent even of spare
encodings, so this public field transfers unconditionally. -/
theorem left_signal_mask {p c : Nat} (u v : Site p c) :
    full (signalF p c) (pubMask (u,v)).1 true := by
  intro j hj
  have H := (lane_support (signalF p c) ((signalF p c).offset+j)).mpr
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left hj _⟩
  change (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(4+q c))).getLsbD (4+q c+j)=true at H
  change (pubMask (u,v)).1.getLsbD (4+q c+j)=true
  unfold pubMask
  dsimp only
  simp only [BitVec.getLsbD_or,H,Bool.or_true,Bool.true_or]

theorem raw_left_signal {p c : Nat} (hp : 0<p)
    (x : Pair (BitVec (publicWidth p c))) :
    (readPub hp ((publicWork hp x).1.apply x.1)).signal =
      (pairStep (readPub hp x.1) (readPub hp x.2)).1.signal := by
  let y := (pairStep (readPub hp x.1) (readPub hp x.2)).1
  have bit : full (signalF p c) (publicWork hp x).1.mask true :=
    left_signal_mask (readPub hp x.1) (readPub hp x.2)
  change signalDecode ((signalF p c).read ((publicWork hp x).1.apply x.1))=y.signal
  rw [read_patch_write _ _ _ bit]
  change signalDecode ((signalF p c).read (packPub y))=y.signal
  rw [read_pack_signal]
  cases y.signal <;> rfl

/-- A field is either completely issued, or completely held AND
independently unchanged by the typed operation. -/
def FieldCase {w k} (f : Field w k) (m : BitVec w) (same : Prop) : Prop :=
  full f m true ∨ (full f m false ∧ same)

structure EndpointFrame {p c} (m : BitVec (publicWidth p c))
    (old new : Site p c) : Prop where
  residue : FieldCase (residueF p c) m (old.residue=new.residue)
  mark : FieldCase (markF p c) m (old.mark=new.mark)
  leader : FieldCase (leaderF p c) m (old.leader=new.leader)
  bullet : FieldCase (bulletF p c) m (old.bullet=new.bullet)
  shield : FieldCase (shieldF p c) m (old.shield=new.shield)
  signal : FieldCase (signalF p c) m (old.signal=new.signal)
  stock : FieldCase (stockF p c) m (old.stock=new.stock)
  source : FieldCase (sourceF p c) m (old.source=new.source)
  rail : FieldCase (railF p c) m (old.rail=new.rail)

/-- Exact representation transfer once the literal row frame has been
shown, without equating arbitrary spare encodings to canonical packs. -/
theorem endpoint_transfer {p c : Nat} (hp : 0<p) (raw : BitVec (publicWidth p c))
    (new : Site p c) (m : BitVec (publicWidth p c))
    (H : EndpointFrame m (readPub hp raw) new) :
    readPub hp ((⟨m,packPub new⟩ : Patch (publicWidth p c)).apply raw)=new := by
  let patch : Patch (publicWidth p c) := ⟨m,packPub new⟩
  have h_residue : (readPub hp (patch.apply raw)).residue=new.residue :=
    decoded_field (residueDecode hp) (residueF p c) patch raw new.residue
      (congrArg Site.residue (read_pack hp new)) H.residue
  have h_mark : (readPub hp (patch.apply raw)).mark=new.mark :=
    decoded_field (fun a => a.getLsbD 0) (markF p c) patch raw new.mark
      (congrArg Site.mark (read_pack hp new)) H.mark
  have h_leader : (readPub hp (patch.apply raw)).leader=new.leader :=
    decoded_field (fun a => a.getLsbD 0) (leaderF p c) patch raw new.leader
      (congrArg Site.leader (read_pack hp new)) H.leader
  have h_bullet : (readPub hp (patch.apply raw)).bullet=new.bullet :=
    decoded_field (bulletDecode) (bulletF p c) patch raw new.bullet
      (congrArg Site.bullet (read_pack hp new)) H.bullet
  have h_shield : (readPub hp (patch.apply raw)).shield=new.shield :=
    decoded_field (fun a => a.getLsbD 0) (shieldF p c) patch raw new.shield
      (congrArg Site.shield (read_pack hp new)) H.shield
  have h_signal : (readPub hp (patch.apply raw)).signal=new.signal :=
    decoded_field (signalDecode) (signalF p c) patch raw new.signal
      (congrArg Site.signal (read_pack hp new)) H.signal
  have h_stock : (readPub hp (patch.apply raw)).stock=new.stock :=
    decoded_field (fun a => a.getLsbD 0) (stockF p c) patch raw new.stock
      (congrArg Site.stock (read_pack hp new)) H.stock
  have h_source : (readPub hp (patch.apply raw)).source=new.source :=
    decoded_field (fun a => sourceDecode (2*c) a.toNat) (sourceF p c) patch raw new.source
      (congrArg Site.source (read_pack hp new)) H.source
  have h_rail : (readPub hp (patch.apply raw)).rail=new.rail :=
    decoded_field (railDecode) (railF p c) patch raw new.rail
      (congrArg Site.rail (read_pack hp new)) H.rail
  cases h : readPub hp (patch.apply raw) with
  | mk ro ma le bu sh si st so ra =>
    rw [h] at h_residue h_mark h_leader h_bullet h_shield h_signal h_stock h_source h_rail
    cases new
    dsimp only at *
    subst_vars
    rfl

/-- Complete all-byte publicWork transfer reduces to two typed frames
for the actual public masks and literal pairStep, not to finite samples. -/
theorem pair_transfer_of_frame {p c : Nat} (hp : 0<p)
    (x : Pair (BitVec (publicWidth p c)))
    (H : let old := Pair.map (readPub hp) x
         let new := pairStep old.1 old.2
         let m := pubMask old
         EndpointFrame m.1 old.1 new.1 ∧ EndpointFrame m.2 old.2 new.2) :
    Pair.map (readPub hp) (patchPair (publicWork hp x) x) =
      pairStep (readPub hp x.1) (readPub hp x.2) := by
  apply Prod.ext
  · exact endpoint_transfer hp x.1 _ _ H.1
  · exact endpoint_transfer hp x.2 _ _ H.2

end L4.BStarPublicFrame

