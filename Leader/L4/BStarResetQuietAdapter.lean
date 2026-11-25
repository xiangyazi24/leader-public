import Leader.L4.BStarResetMarkAdapter
import Leader.L4.BStarResetChartIndex
import Leader.L4.BStarResetIdleRing

namespace L4.BStarResetQuietAdapter
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongDoor BStarLongEvents
open BStarH6WordChart BStarAcquireForwardTrace
open BStarResetRailRing BStarSeparatingRail BStarResetMarkAdapter
open BStarResetQuietTable BStarResetQuiet BStarResetIdleRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem live_f (op : Nat) (ho : op<3) (t : Token) (F : (resetTag op).F t) :
    ResetLive t := by
  obtain ⟨p,H,rfl⟩ := F
  exact .f p (reset_of_holds op ho p H)

theorem live_d (op : Nat) (ho : op<3) (t : Token) (D : (resetTag op).D t) :
    ResetLive t := by
  obtain ⟨p,H,rfl⟩ := D
  exact .d p (reset_of_holds op ho p H)

theorem root_before_reply {op : Nat} {len : Nat} {rail : BStarSeparatingRail.Rail} {z : Cursor}
    (G : Good (resetTag op) len rail z) (h : z≠.back 0) :
    rail 0=.trail ∨ (resetTag op).F (rail 0) := by
  cases z with
  | out k =>
    by_cases K : k=0
    · exact .inr (K ▸ G.2.1)
    · exact .inl (G.2.2 0 (by omega))
  | back k =>
    have H : 0<k := by cases k <;> simp_all
    exact .inl (G.2.2.1 0 H)

/-- Door safety at any touched address of an owner before its first
tagged source reply. Incidence needed only when it is right H6 K0. -/
theorem pair_door_safe (x : XX) (e : Fin n) (addr : Nat → BStarAcquireVisitOrder.Pos n)
    (a : AtK) (j len op : Nat) (ho : op<3) (z : Cursor)
    (G : Good (resetTag op) len (project addr x) z) (notReply : z≠.back 0)
    (addressed : addr j=address e a)
    (root : a=R 0 → oldH6 B x (rightNeighbor e)=true → j=0)
    (waitValid : a=R 0 → oldH6 B x (rightNeighbor e)=true →
      LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (waitPhase : a=R 0 → oldH6 B x (rightNeighbor e)=true →
      (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2) :
    DoorSafe (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) a := by
  by_cases ar : a=R 0
  · subst a
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    refine ⟨waitValid,?_⟩
    intro _ C t hC _
    have cm : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨(C,.door t),hC,rfl⟩
    have CQ := BStarK0Frame.door_eq g raw C t hC
    have Ch : g.2.axes.h6=true :=
      (BStarResetChartIndex.selected_door g C cm (by rw [CQ.1]; rfl)).2.1
    have hv := waitValid rfl Ch
    have hw := waitPhase rfl Ch
    have Addr := root rfl Ch
    subst j
    have rt := root_before_reply G notReply
    rcases rt with H|F
    · have Rw : atSite raw.2 0=.trail := (old_read x e (R 0)).trans
        ((congrArg (atCursor x) addressed).symm.trans H)
      obtain ⟨rfl,rfl⟩ := CQ
      change oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold
      rw [Rw]
      exact wait_holds_trail raw.2 hv hw
    · obtain ⟨pay,H,P⟩ := F
      have Rw : atSite raw.2 0=.forward pay := (old_read x e (R 0)).trans
        ((congrArg (atCursor x) addressed).symm.trans P)
      obtain ⟨rfl,rfl⟩ := CQ
      change oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold
      rw [Rw,BStarResetTaggedRows.bind_reset _ _ _ (reset_of_holds op ho pay H)]
      exact wait_holds_forward raw.2 pay hv hw
  · exact safe_nonright _ _ _ ar

/-- Geometric data for quiet frames. DoorSafe concerns only a touched
K0, and is derived from a valid source WAIT and the live cursor. -/
structure MarkFrames (x : XX) (e : Fin n) (addr : Nat → BStarAcquireVisitOrder.Pos n) (len : Nat) : Prop where
  safe : ∀ j≤len, ∀ a : AtK, addr j=address e a →
    a∉discarded (oldPair B x e) ∧
    DoorSafe (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) a
  idle_avoids : ∀ j≤len, ∀ a : AtK, addr j=address e a →
    ¬linkAt hp x e addr len j →
    (∀ i, i+1=j → ¬linkAt hp x e addr len i) →
    (j=len → ¬onTerminal hp x e addr len) →
    avoids a (middle (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))

private theorem bound_eq (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (H : quiet (readK raw a) ∨ ResetLive (readK raw a)) :
    bound g (readK raw) a=readK raw a :=
  H.elim (quiet_bound g (readK raw) a) (live_bind _ _ _)

private theorem addr_cases (e : Fin n) (v : BStarAcquireVisitOrder.Pos n) :
    (∃ a : AtK, v=address e a) ∨ (v.1≠e ∧ v.1≠rightNeighbor e) := by
  by_cases l : v.1=e
  · exact .inl ⟨L v.2,Prod.ext l rfl⟩
  · by_cases r : v.1=rightNeighbor e
    · exact .inl ⟨R v.2,Prod.ext r rfl⟩
    · exact .inr ⟨l,r⟩

/-- Exact decoded quiet table for the actual mark. Unlike raw byte
identity, token identity permits ignored spare bits to normalize. -/
theorem quiet_of_frames_for (x : XX) (e : Fin n) (he : e≠rightNeighbor e)
    (addr : Nat → BStarAcquireVisitOrder.Pos n) (len op : Nat) (ho : op<3)
    (MF : MarkFrames hp x e addr len) (tag : Tag)
    (toF : ∀ t, tag.F t → (resetTag op).F t)
    (toD : ∀ t, tag.D t → (resetTag op).D t) :
    Quiet tag len (project addr x) (project addr (AllSizeS1Geometry.step B x e))
      (linkAt hp x e addr len) (onTerminal hp x e addr len) := by
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  let y := AllSizeS1Geometry.step B x e
  let U := project addr x
  let W := project addr y
  have read (j : Nat) (a : AtK) (H : addr j=address e a) : readK raw a=U j :=
    (old_read x e a).trans ((congrArg (atCursor x) H).symm)
  have idle {j : Nat} (hj : j≤len)
      (A : ¬linkAt hp x e addr len j) (D : ∀ i, i+1=j → ¬linkAt hp x e addr len i)
      (T : j=len → ¬onTerminal hp x e addr len)
      (h : quiet (U j) ∨ ResetLive (U j)) : W j=U j := by
    rcases addr_cases e (addr j) with ⟨a,H⟩|⟨nl,nr⟩
    · obtain ⟨nd,ds⟩ := MF.safe j hj a H
      have Rw : quiet (readK raw a) ∨ ResetLive (readK raw a) := (read j a H).symm ▸ h
      have F := idle_at hp x e he a Rw nd (MF.idle_avoids j hj a H A D T) ds
      exact (congrArg (atCursor y) H).trans (F.trans (congrArg (atCursor x) H).symm)
    · exact idle_off_pair hp x e (addr j) nl nr
  have links {j : Nat} (Lh : linkAt hp x e addr len j)
      (h1 : quiet (U j) ∨ ResetLive (U j)) (h2 : quiet (U (j+1)) ∨ ResetLive (U (j+1)))
      (H : LinkHold (U j) (U (j+1))) : W j=U j ∧ W (j+1)=U (j+1) := by
    obtain ⟨J,C,d,M,hd,S,D⟩ := Lh
    have HK := (BStarAcquireReturn.link_shape g C d M hd).2.1
    have h1' : quiet (readK raw C.source) ∨ ResetLive (readK raw C.source) :=
      (read j C.source S).symm ▸ h1
    have h2' : quiet (readK raw d) ∨ ResetLive (readK raw d) :=
      (read (j+1) d D).symm ▸ h2
    have Bnd : LinkHold (bound g (readK raw) C.source) (bound g (readK raw) d) := by
      rw [bound_eq g raw C.source h1',bound_eq g raw d h2',read j C.source S,read (j+1) d D]
      exact H
    obtain ⟨nd,ds⟩ := MF.safe j (by omega) C.source S
    obtain ⟨nd',ds'⟩ := MF.safe (j+1) (by omega) d D
    have U1 := idle_link hp x e he C d C.source M HK hd Bnd (.inl rfl) h1' nd ds
    have U2 := idle_link hp x e he C d d M HK hd Bnd (.inr rfl) h2' nd' ds'
    exact ⟨(congrArg (atCursor y) S).trans (U1.trans (congrArg (atCursor x) S).symm),
      (congrArg (atCursor y) D).trans (U2.trans (congrArg (atCursor x) D).symm)⟩
  have term (Q : onTerminal hp x e addr len) (h : quiet (U len) ∨ ResetLive (U len))
      (K : TerminalHold (U len)) : W len=U len := by
    obtain ⟨C,M,hk,_,_,S⟩ := Q
    obtain ⟨nd,ds⟩ := MF.safe len (by omega) C.source S
    have hh : quiet (readK raw C.source) ∨ ResetLive (readK raw C.source) :=
      (read len C.source S).symm ▸ h
    have H : TerminalHold (bound g (readK raw) C.source) := by
      rw [bound_eq g raw C.source hh,read len C.source S]
      exact K
    have V := idle_terminal hp x e he C M hk H hh nd ds
    exact (congrArg (atCursor y) S).trans (V.trans (congrArg (atCursor x) S).symm)
  change Quiet _ len U W _ _
  refine { idle := ?_, tt := ?_, ee := ?_, tf := ?_, de := ?_, termD := ?_, termE := ?_ }
  · intro j hj A D T
    exact ⟨fun s => (idle hj A D T (.inl (.inr s))).trans s,
      fun s => (idle hj A D T (.inl (.inl s))).trans s,
      fun f => (idle hj A D T (.inr (live_f op ho _ (toF _ f)))).symm ▸ f,
      fun d => (idle hj A D T (.inr (live_d op ho _ (toD _ d)))).symm ▸ d⟩
  · intro j Lh t q
    have H := links Lh (.inl (.inr t)) (.inl (.inr q)) (by rw [t,q]; exact .tt)
    exact ⟨H.1.trans t,H.2.trans q⟩
  · intro j Lh t q
    have H := links Lh (.inl (.inl t)) (.inl (.inl q)) (by rw [t,q]; exact .ee)
    exact ⟨H.1.trans t,H.2.trans q⟩
  · intro j Lh t f
    have HH : LinkHold (U j) (U (j+1)) := by
      obtain ⟨p,_,K⟩ := toF _ f
      rw [t,K]
      exact .tf p
    have H := links Lh (.inl (.inr t)) (.inr (live_f op ho _ (toF _ f))) HH
    exact ⟨H.1.trans t,H.2.symm ▸ f⟩
  · intro j Lh d t
    have HH : LinkHold (U j) (U (j+1)) := by
      obtain ⟨p,S,K⟩ := toD _ d
      obtain ⟨q,eq⟩ := (BStarResetTaggedRows.bind_finish g.1 0 p (reset_of_holds op ho p S)).2
      rw [t,K,eq]
      exact .de q
    have H := links Lh (.inr (live_d op ho _ (toD _ d))) (.inl (.inl t)) HH
    exact ⟨H.1.symm ▸ d,H.2.trans t⟩
  · intro Q d
    have K : TerminalHold (U len) := by
      obtain ⟨p,S,Z⟩ := toD _ d
      obtain ⟨q,eq⟩ := (BStarResetTaggedRows.bind_finish g.1 0 p (reset_of_holds op ho p S)).2
      rw [Z,eq]
      exact .d q
    exact (term Q (.inr (live_d op ho _ (toD _ d))) K).symm ▸ d
  · intro Q O
    exact (term Q (.inl (.inl O)) (by rw [O]; exact .e)).trans O

theorem quiet_of_frames (x : XX) (e : Fin n) (he : e≠rightNeighbor e)
    (addr : Nat → BStarAcquireVisitOrder.Pos n) (len op : Nat) (ho : op<3)
    (MF : MarkFrames hp x e addr len) :
    Quiet (resetTag op) len (project addr x) (project addr (AllSizeS1Geometry.step B x e))
      (linkAt hp x e addr len) (onTerminal hp x e addr len) :=
  quiet_of_frames_for hp x e he addr len op ho MF (resetTag op) (fun _ h => h) (fun _ h => h)

end L4.BStarResetQuietAdapter
