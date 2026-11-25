import Leader.L4.BStarLongFencePrefix

namespace L4.BStarLongFenceTopology
open AllSizeProtocol BStarLongClaims BStarLongCommandData

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- The literal departing FENCE port and the selected data incidence
have the same orientation. The old FENCE lane cannot be a data
destination on that very edge, even on aliased seam and END rows. -/
theorem no_incoming_on_fence_edge (g : Pair LongGeometry)
    (C : CommandClaim) (D : DataClaim) (s : Sheet)
    (hC : C∈commandClaims g) (hD : D∈dataClaims g)
    (hs : fenceSheet (BStarLongCommand.geometry g C.source.side) C.source.occurrence=some s) :
    D.destination≠some ⟨C.source.side,s⟩ := by
  obtain ⟨x,y⟩ := g
  have H (g : Pair LongGeometry) :
      (commandClaims g).all (fun c =>
        match fenceSheet (BStarLongCommand.geometry g c.source.side) c.source.occurrence with
        | none => true
        | some s => (dataClaims g).all (fun d => d.destination != some ⟨c.source.side,s⟩)) =true := by
    clear hC hD hs
    obtain ⟨x,y⟩ := g
    have R : (commandClaims (x,y)).all (fun c =>
        match fenceSheet (BStarLongCommand.geometry (x,y) c.source.side) c.source.occurrence with
        | none => true
        | some s => (dataClaims (x,y)).all (fun d => d.destination != some ⟨c.source.side,s⟩)) =
      (commandClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false)).all (fun c =>
        match fenceSheet (BStarLongCommand.geometry
          (geo false x.inside x.last,geo y.axes.h6 y.inside false) c.source.side) c.source.occurrence with
        | none => true
        | some s => (dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false)).all
            (fun d => d.destination != some ⟨c.source.side,s⟩)) := by
      have A : commandClaims (x,y)=commandClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
      have B : dataClaims (x,y)=dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
      rw [A,B]
      apply congrArg (List.all _)
      funext c
      generalize c.source.side=s
      cases s <;> rfl
    rw [R]
    generalize x.inside=xi
    generalize x.last=xl
    generalize y.axes.h6=yh
    generalize y.inside=yi
    cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel
  have q := List.all_eq_true.mp (H (x,y)) C hC
  rw [hs] at q
  exact bne_iff_ne.mp (List.all_eq_true.mp q D hD)

open BStarLongPackets BStarLongPrep BStarLongFencePrefix

private theorem offered_mem {α : Type} (key : α → Nat) (l : List α) (a : α)
    (ha : a∈offers key l) : a∈l := by
  induction l with
  | nil => exact ha
  | cons b l ih =>
    change a∈insert key b (offers key l) at ha
    rcases (mem_insert key b a (offers key l)).mp ha with h|h
    · exact List.mem_cons.mpr (.inl h)
    · exact List.mem_cons_of_mem _ (ih h)

theorem selected_data_raw (g : Pair LongGeometry) (Rsv : List (At Sheet)) (D : DataClaim)
    (h : D∈orderedData g Rsv) : D∈dataClaims g := by
  apply offered_mem dataKey
  exact (select_sublist Claim.slots Rsv (offers dataKey (dataClaims g))).subset h

theorem selected_command_raw (g : Pair LongGeometry) (C : CommandClaim)
    (h : C∈orderedCommands g) : C∈commandClaims g := by
  apply offered_mem commandKey
  exact (select_sublist Claim.slots [] (offers commandKey (commandClaims g))).subset h

/-- On the literal departing mark itself the newly passed lane does
not need any traffic or provenance premise. The only remaining
same-mark proviso is that no preparation claims the lane. -/
theorem passing_lane_frames (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (C : CommandClaim) (p : BStarLongToken.Payload) (s : Sheet)
    (hC : C∈orderedCommands g) (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (hs : fenceSheet (BStarLongCommand.geometry g C.source.side) C.source.occurrence=some s)
    (ha : checkFence g (view x) C.source p=.advance)
    (noPrep : (⟨C.source.side,s⟩ : At Sheet)∉reserved (round g x).prep) :
    let lane : At Sheet := ⟨C.source.side,s⟩
    view (patchPair (patch g x) x) lane=view x lane := by
  apply passed_lane_frame g x _
    ((mapped_fence_passes g (view x) C.source p s hf ho hs).mp ha) noPrep
  intro d hD hd
  exact (no_incoming_on_fence_edge g C d s (selected_command_raw g C hC)
    (selected_data_raw g _ d hD) hs hd).elim

/-- Any actual reservation of this sheet comes from a genuinely
checked old advancing command, with the exact hardwired prep opcode
and old local lane won by arbitration. In particular it cannot arise
from the FENCE token merely being present. -/
theorem reserved_from_old_advance (g : Pair LongGeometry)
    (x : Pair (BitVec BStarTrace.LW)) (s : At Sheet)
    (h : s∈reserved (round g x).prep) :
    ∃ c p op, (c,BStarLongCommand.Offer.advance p)∈gated g x ∧
      p.fault=0 ∧ prepOf p.opcode.toNat=some op ∧
      s.side=c.source.side ∧ s.occurrence∈prepSites
        (BStarLongCommand.geometry g c.source.side) c.source.occurrence op := by
  obtain ⟨o,hw,he⟩ := List.mem_map.mp h
  have hm : o∈(round g x).prep := by
    change o∈(arbitration (round g x).prep).1 at hw
    unfold arbitration at hw
    rw [arbitrate_winners] at hw
    apply offered_mem offerPriority
    exact (select_sublist (fun a : Offer => [a.claim.lane]) []
      (offers offerPriority (round g x).prep)).subset hw
  change o∈preparedBy g x (gated g x) at hm
  unfold preparedBy at hm
  obtain ⟨⟨b,t⟩,hgate,ho⟩ := List.mem_flatMap.mp hm
  cases t <;> simp only at ho
  all_goals try cases ho
  rename_i p
  unfold fieldOffers at ho
  split at ho
  · cases ho
  · rename_i hf
    split at ho
    · cases ho
    · rename_i op hop
      obtain ⟨c,hc,hEq⟩ := List.mem_map.mp ho
      subst o
      obtain ⟨sheet,hSheet,hCS⟩ := List.mem_map.mp hc
      subst c
      subst s
      exact ⟨b,p,op,hgate,by simpa using hf,hop,rfl,hSheet⟩

/-- A mapped FENCE finish needs no assumed packet-traffic premise,
and its prep premise can be discharged by excluding overlapping old
advancing prep origins (the precise generated custody obligation). -/
theorem passing_lane_frames_of_origin (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (C : CommandClaim) (p : BStarLongToken.Payload) (s : Sheet)
    (hC : C∈orderedCommands g) (hf : p.fault=0) (ho : p.opcode.toNat=11)
    (hs : fenceSheet (BStarLongCommand.geometry g C.source.side) C.source.occurrence=some s)
    (ha : checkFence g (view x) C.source p=.advance)
    (exclude : ∀ c q op, (c,BStarLongCommand.Offer.advance q)∈gated g x →
      q.fault=0 → prepOf q.opcode.toNat=some op → C.source.side=c.source.side →
      s∉prepSites (BStarLongCommand.geometry g c.source.side) c.source.occurrence op) :
    let lane : At Sheet := ⟨C.source.side,s⟩
    view (patchPair (patch g x) x) lane=view x lane := by
  apply passing_lane_frames g x C p s hC hf ho hs ha
  intro H
  obtain ⟨c,q,op,h1,h2,h3,h4,h5⟩ := reserved_from_old_advance g x _ H
  exact exclude c q op h1 h2 h3 h4 h5

end L4.BStarLongFenceTopology
