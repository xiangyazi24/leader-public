import Leader.L4.BStarBankWork
import Leader.L4.BStarStageLive

/-! One-mark preservation of a captured bank through the *whole*
concrete long row. The remaining temporal premise is explicit:
any selected STAGE must still refer to this owner's captured bank,
and the holding interval stops before publication at that endpoint. -/
namespace L4.BStarBankTrace
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims BStarBankCapture

def sideFlag (s : Side) : Bool := s==.right
def sideFrame (s : Side) (b : Fin 3) (w : Bool × Patch LW) : Prop :=
  w.1=sideFlag s → Protected b w.2

theorem k_protects (b : Fin 3) (w : KWrite) : Protected b (lowerOne w).2 := by
  apply BStarBankWork.of_beforeBank
  unfold lowerOne setToken
  apply BStarBankWork.assign
  exact Nat.le_trans (k_before_file _) (by decide)

theorem nonheader_protects (b : Fin 3) (g : LongGeometry) : Protected b (nonheader g) := by
  unfold nonheader
  split
  · exact frame_empty _
  · exact frame_compose
      (BStarBankWork.of_beforeBank
        (BStarBankWork.compose
          (BStarBankWork.compose (BStarBankWork.assign _ _ (by decide))
            (BStarBankWork.assign _ _ (by decide))) (BStarBankWork.assign _ _ (by decide))) b)
      (frame_compose (frame_stage_field _ _) (frame_seal_field _ _))

theorem grant_site_protects (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (s : Side) (b : Fin 3) :
    ∀ w∈(BStarLongGrant.siteWrites g x os s).map Write.patch, Protected b w.2 := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  obtain ⟨j,_,hh⟩ := List.mem_filterMap.mp hv
  split at hh
  · cases hh
    apply frame_assign
    · right
      have hb := b.isLt
      have hj := j.isLt
      simp only [bankBase,grant]
      omega
    · left
      simp only [grant]
      omega
  · contradiction

theorem grant_protects (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (b : Fin 3) :
    ∀ w∈(BStarLongGrant.run g x os).writes.map Write.patch, Protected b w.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro w h
  exact h.elim (grant_site_protects g x os .left b w) (grant_site_protects g x os .right b w)

theorem packet_protects (a : At Sheet) (v : BStarLongPackets.Leaf)
    (b : Fin 3) : Protected b (BStarLongPackets.writeAt a v).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarBankWork.of_beforeBank
  apply BStarBankWork.assign
  have := v.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index a.occurrence).val)+v.offset+v.width≤2222
  omega

theorem copy_protects (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (os : List BStarLongPrep.Offer) (b : Fin 3) :
    ∀ w∈(BStarLongPrep.writes g old os).map Write.patch, Protected b w.2 := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hv
  exact packet_protects a u b

def beforeOutgoing (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) (p : Payload) :=
  BStarLongArithmetic.visit (BStarLongCommand.geometry g c.source.side) c.source.occurrence
    (atOld x c.source) p

def outEffect (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) (p : Payload) :=
  BStarLongOutgoing.execute (BStarLongCommand.geometry g c.source.side) c.source.occurrence
    (atOld x c.source) (beforeOutgoing g x c p).2

def StageLiveAt (g : Pair LongGeometry) (x : Pair (BitVec LW)) (b : Fin 3)
    (c : CommandClaim) (p : Payload) : Prop :=
  BStarStageLive.StageLiveOwned (BStarLongCommand.geometry g c.source.side)
    c.source.occurrence (atOld x c.source) b (beforeOutgoing g x c p).2

def SafeOffer (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (o : CmdOffer) : Prop :=
  match o.2 with
  | .advance p => o.1.source.side=s →
    StageLiveAt g x b o.1 p ∧ (outEffect g x o.1 p).published=none
  | _ => True

theorem selected_protects (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (b : Fin 3) (o : CmdOffer) (ho : SafeOffer g x s b o) :
    ∀ w∈(selected g x o).work, sideFrame s b w := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [selected]
  all_goals try (intro w hw; simp at hw; done)
  · split
    · intro w hw; simp at hw
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact BStarBankWork.of_beforeBank (BStarBankWork.door_frame _ _ _ ‹_›) b
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact BStarBankWork.of_beforeBank (BStarBankWork.accept_frame _ _ _) b
  · rename_i p
    intro w hw eq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact BStarBankWork.of_beforeBank (BStarBankWork.numeric_visit _ _ _ _) b
    · have hs : c.source.side=s := by
        cases h : c.source.side <;> cases s <;> simp_all [sideFlag]
      obtain ⟨hz,hn⟩ := ho hs
      exact BStarStageLive.outgoing_live_protects _ _ _ _ b hz hn

theorem selected_fold_protects (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (b : Fin 3) (os : List CmdOffer) (acc : Selected)
    (safe : ∀ o∈os, SafeOffer g x s b o) (H : ∀ w∈acc.work, sideFrame s b w) :
    ∀ w∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work, sideFrame s b w := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih
    · intro a ha; exact safe a (List.mem_cons_of_mem _ ha)
    · intro w hw
      exact (List.mem_append.mp hw).elim (H w)
        (selected_protects g x s b o (safe o List.mem_cons_self) w)

def offers (g : Pair LongGeometry) (x : Pair (BitVec LW)) : List CmdOffer :=
  (BStarLongGrant.run g x (BStarLongCommandData.round g x).offered).departures

theorem longWork_protects (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (b : Fin 3) (safe : ∀ o∈offers g x, SafeOffer g x s b o) :
    Protected b (lane (sideFlag s) (longWork g x)) := by
  have routine : ∀ w∈(longTrace g x).assignments, sideFrame s b w := by
    intro w hw
    unfold longTrace at hw
    simp only [List.mem_append] at hw
    rcases hw with (((((hf|hc)|hg)|hd)|hw)|hl)
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hf
      exact fun _ => k_protects b q
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact fun _ => nonheader_protects b g.1
      · exact fun _ => nonheader_protects b g.2
    · exact fun _ => grant_protects g x _ b w hg
    · exact fun _ => copy_protects g _ _ b w hd
    · exact selected_fold_protects g x s b _ _ safe (by simp) w hw
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hl
      exact fun _ => k_protects b q
  have held (i : Nat) (hh : (bankBase b≤i ∧ i<bankBase b+45) ∨ (2360≤i ∧ i<2362)) :
      (lane (sideFlag s) (longWork g x)).mask.getLsbD i=false := by
    rw [exact_assignment_mask]
    apply Bool.eq_false_iff.mpr
    intro hai
    obtain ⟨w,hw,hf⟩ := List.any_eq_true.mp hai
    obtain ⟨hs,hm⟩ := Bool.and_eq_true_iff.mp hf
    have F := routine w hw (beq_iff_eq.mp hs)
    rcases hh with ⟨l,r⟩|⟨l,r⟩
    · simp [F.1 i l r] at hm
    · simp [F.2 i l r] at hm
  exact ⟨fun i l r => held i (.inl ⟨l,r⟩), fun i l r => held i (.inr ⟨l,r⟩)⟩

theorem longWork_operand (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (b : Fin 3) (safe : ∀ o∈offers g x, SafeOffer g x s b o) :
    let y := lane (sideFlag s) (patchPair (longWork g x) x)
    let u := lane (sideFlag s) x
    selector.read y=selector.read u ∧
      (∀ f, (bankDigit b f).read y=(bankDigit b f).read u) ∧
      (∀ f, (bankHeader b f).read y=(bankHeader b f).read u) := by
  have F := longWork_protects g x s b safe
  have eq : lane (sideFlag s) (patchPair (longWork g x) x) =
      (lane (sideFlag s) (longWork g x)).apply (lane (sideFlag s) x) := by
    cases s <;> rfl
  rw [eq]
  exact ⟨selector_read F _,digit_read F _,header_read F _⟩

#print axioms longWork_protects
#print axioms longWork_operand
end L4.BStarBankTrace
