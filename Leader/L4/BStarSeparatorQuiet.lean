import Leader.L4.BStarSeparatorIdleClass

/-! Quiet/parked-aware geometry framing on a real fixed owner chart. -/
namespace L4.BStarSeparatorQuiet
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongDoor BStarLongEvents
open BStarH6WordChart BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarAcquireAnchors BStarLongFixedRouting
open BStarResetRailRing BStarSeparatingRail BStarResetMarkAdapter
open BStarResetQuietAdapter BStarResetQuietTable BStarResetQuiet BStarResetIdleRing
open BStarResetChartTouch BStarSeparatorControl BStarSeparatorIdleClass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem frames_any {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) (e : Fin n)
    (z : Cursor) (live : z≠.back 0)
    (G : Good anyTag len (project (fun j => S.getD j fallback) x) z)
    (waitV : LongDoorGuard.valid manifest (x (S.getD 0 fallback).1).long=true)
    (waitP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=2) :
    MarkFrames hp x e (fun j => S.getD j fallback) len := by
  let addr := fun j => S.getD j fallback
  refine ⟨?_,?_⟩
  · intro j hj a hit
    refine ⟨not_discarded hp C same e j hj a hit,?_⟩
    have Rt (h : a=R 0) (hhx : oldH6 B x (rightNeighbor e)=true) : j=0 := by
      subst a
      have hOld : oldH6 B base (rightNeighbor e)=true :=
        (congrArg Prod.fst (same (rightNeighbor e))).trans hhx
      have M : addr j∈S := by
        have L := C.length
        change S.getD j fallback∈S
        rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
        exact List.getElem_mem _
      have Own := (C.entries _ M).2
      change addr j=address e (R 0) at hit
      rw [hit] at Own
      have atRoot := (endpoint_spec _ hh o 0).2.2 (rightNeighbor e) hOld Own
      have eq : addr j=addr 0 := hit.trans (atRoot.trans C.root.symm)
      have L := C.length
      exact (List.getD_inj (by omega) (by omega) C.nodup).mp eq
    by_cases E : a=R 0
    · subst a
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      have cfg (J : g.2.axes.h6=true) : (addr 0).1=rightNeighbor e := by
        have A := Rt rfl J
        exact congrArg Prod.fst (A ▸ hit)
      refine ⟨fun _ J => cfg J ▸ waitV,?_⟩
      intro _ c t hc _
      have cm : c∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨(c,.door t),hc,rfl⟩
      have CQ := BStarK0Frame.door_eq g raw c t hc
      have J : g.2.axes.h6=true :=
        (BStarResetChartIndex.selected_door g c cm (by rw [CQ.1]; rfl)).2.1
      have hv : LongDoorGuard.valid manifest raw.2=true := by
        change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
        rw [←cfg J]; exact waitV
      have hw : (ctrlPhase.read raw.2).toNat=2 := by
        change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2
        rw [←cfg J]; exact waitP
      rw [Rt rfl J] at hit
      obtain ⟨rfl,rfl⟩ := CQ
      have A : readK raw (R 0)=project addr x 0 :=
        (old_read x e (R 0)).trans ((congrArg (atCursor x) hit).symm)
      change oldDoor raw.2 (bound g (readK raw) (R 0))=.hold
      rw [BStarLongTransport.bound,A]
      rcases before_receipt G live with T|⟨p,P⟩
      · rw [T]; exact wait_holds_trail raw.2 hv hw
      · rw [P]
        obtain ⟨q,Q⟩ := bound_F (geometry g (R (0:Fin 11)).side) (R (0:Fin 11)).occurrence p
        rw [Q]
        exact wait_holds_forward raw.2 q hv hw
    · exact safe_nonright _ _ _ E
  · intro j hj a hit noSucc noPred noTerm
    apply middle_avoids_of_chart
    rintro ⟨K,act⟩ hk hSlot w hw _
    have P : K∈orderedCommands (oldPair B x e) := by
      rw [←actualOffers_claims _ ((x e).long,(x (rightNeighbor e)).long)]
      exact List.mem_map.mpr ⟨(K,act),hk,rfl⟩
    rcases touches hp C same e j hj K a P hSlot hit with D|T|L|⟨i,J,L⟩
    · skip
      have hG : BStarLongLiteral.gatedAt (oldPair B x e)
          ((x e).long,(x (rightNeighbor e)).long) K =
          .door (bound (oldPair B x e) (readK ((x e).long,(x (rightNeighbor e)).long)) K.source) := by
        unfold BStarLongLiteral.gatedAt BStarLongLiteral.classifyOld
        simp [D.2.1,classify,BStarLongCommandData.checkOffer,bound,BStarLongCommandData.oldTokens,readK]
      have H := BStarAcquireNonRouting.actual_door _ _ (K,act) hk _ hG
      dsimp only at H
      subst act
      unfold selected at hw
      dsimp only at hw
      split at hw <;> cases hw
    · exact noTerm T.1 T.2
    · exact noSucc L
    · exact noPred i J L

#print axioms frames_any
private theorem addr_cases (e : Fin n) (v : Pos n) :
    (∃ a : AtK, v=address e a) ∨ (v.1≠e ∧ v.1≠rightNeighbor e) := by
  by_cases l : v.1=e
  · exact .inl ⟨L v.2,Prod.ext l rfl⟩
  · by_cases r : v.1=rightNeighbor e
    · exact .inl ⟨R v.2,Prod.ext r rfl⟩
    · exact .inr ⟨l,r⟩

/-- All untouched and selected hold laws through real old marks. F/D
preservation allows normalization and race observation, so neither
arbitrary payload equality nor a reset-specific opcode is needed. -/
theorem quiet_any (x : XX) (e : Fin n) (he : e≠rightNeighbor e)
    (addr : Nat → Pos n) (len : Nat) (MF : MarkFrames hp x e addr len) :
    Quiet anyTag len (project addr x) (project addr (AllSizeS1Geometry.step B x e))
      (linkAt hp x e addr len) (onTerminal hp x e addr len) := by
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  let y := AllSizeS1Geometry.step B x e
  let U := project addr x
  let W := project addr y
  have read (j : Nat) (a : AtK) (H : addr j=address e a) : readK raw a=U j :=
    (old_read x e a).trans ((congrArg (atCursor x) H).symm)
  have class_at {j : Nat} (hj : j≤len) (a : AtK) (H : addr j=address e a)
      (A : avoids a (middle g raw)) : cls (W j)=cls (U j) := by
    obtain ⟨nd,ds⟩ := MF.safe j hj a H
    have N := joined_idle_cls k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) a nd A ds
    have Z : W j=readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a :=
      (congrArg (atCursor y) H).trans (new_read B x e he a).symm
    exact (congrArg cls Z).trans (N.trans (congrArg cls (read j a H)))
  have idle {j : Nat} (hj : j≤len)
      (A : ¬linkAt hp x e addr len j) (D : ∀ i, i+1=j → ¬linkAt hp x e addr len i)
      (T : j=len → ¬onTerminal hp x e addr len) : cls (W j)=cls (U j) := by
    rcases addr_cases e (addr j) with ⟨a,H⟩|⟨nl,nr⟩
    · exact class_at hj a H (MF.idle_avoids j hj a H A D T)
    · exact congrArg cls (idle_off_pair hp x e (addr j) nl nr)
  have links {j : Nat} (Lh : linkAt hp x e addr len j)
      (H : ∀ (s t : AtK), readK raw s=U j → readK raw t=U (j+1) →
        LinkHold (bound g (readK raw) s) (bound g (readK raw) t)) :
      cls (W j)=cls (U j) ∧ cls (W (j+1))=cls (U (j+1)) := by
    obtain ⟨J,C,d,M,hd,S,D⟩ := Lh
    have HK := (BStarAcquireReturn.link_shape g C d M hd).2.1
    obtain ⟨A,Q⟩ := link_avoids g raw C d M HK hd (H _ _ (read j _ S) (read (j+1) _ D))
    exact ⟨class_at (by omega) _ S A,class_at (by omega) _ D Q⟩
  have term (Q : onTerminal hp x e addr len)
      (K : ∀ s : AtK, readK raw s=U len → TerminalHold (bound g (readK raw) s)) :
      cls (W len)=cls (U len) := by
    obtain ⟨C,M,hk,_,_,S⟩ := Q
    exact class_at (Nat.le_refl _) _ S (terminal_avoids g raw C M hk (K _ (read len _ S)))
  change Quiet _ len U W _ _
  refine { idle := ?_, tt := ?_, ee := ?_, tf := ?_, de := ?_, termD := ?_, termE := ?_ }
  · intro j hj A D T
    exact preserves (idle hj A D T)
  · intro j Lh t q
    obtain ⟨H,J⟩ := links Lh (fun s v E F => by rw [bound,E,t,bound,F,q]; exact .tt)
    exact ⟨(preserves H).1 t,(preserves J).1 q⟩
  · intro j Lh t q
    obtain ⟨H,J⟩ := links Lh (fun s v E F => by rw [bound,E,t,bound,F,q]; exact .ee)
    exact ⟨(preserves H).2.1 t,(preserves J).2.1 q⟩
  · intro j Lh t f
    have K : ∀ (s v : AtK), readK raw s=U j → readK raw v=U (j+1) →
        LinkHold (bound g (readK raw) s) (bound g (readK raw) v) := by
      intro s v E F
      obtain ⟨p,P⟩ := f
      rw [bound,E,t,bound,F,P]
      obtain ⟨q,Q⟩ := bound_F (geometry g v.side) v.occurrence p
      rw [Q]
      exact .tf q
    obtain ⟨H,J⟩ := links Lh K
    exact ⟨(preserves H).1 t,(preserves J).2.2.1 f⟩
  · intro j Lh d t
    have K : ∀ (s v : AtK), readK raw s=U j → readK raw v=U (j+1) →
        LinkHold (bound g (readK raw) s) (bound g (readK raw) v) := by
      intro s v E F
      obtain ⟨p,P⟩ := d
      rw [bound,E,P,bound,F,t]
      obtain ⟨q,Q⟩ := bound_D (geometry g s.side) s.occurrence p
      rw [Q]
      exact .de q
    obtain ⟨H,J⟩ := links Lh K
    exact ⟨(preserves H).2.2.2 d,(preserves J).2.1 t⟩
  · intro Q d
    have K : ∀ s : AtK, readK raw s=U len → TerminalHold (bound g (readK raw) s) := by
      intro s E
      obtain ⟨p,P⟩ := d
      rw [bound,E,P]
      obtain ⟨q,Q⟩ := bound_D (geometry g s.side) s.occurrence p
      rw [Q]
      exact .d q
    exact (preserves (term Q K)).2.2.2 d
  · intro Q t
    exact (preserves (term Q (fun s E => by rw [bound,E,t]; exact .e))).2.1 t

#print axioms quiet_any
end L4.BStarSeparatorQuiet
