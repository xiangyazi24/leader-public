import Leader.L4.BStarSeparatorTags
import Leader.L4.BStarClearanceDataChart
import Leader.L4.BStarClearanceObserveJoined

/-! Literal causes for a nominated old forward to wait. Occupancy here
includes BAD, and only a genuine mapped healthy FENCE can block. -/
namespace L4.BStarClearanceBlockade
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongTransport
open BStarLongFiberOwner BStarClearanceDataChart BStarLongPackets

theorem fence_hold_iff (x : Lane) (r : Bool) :
    fence x r = .hold ↔ x.gate=true ∧ x.error=false ∧ x.mobile≠.empty := by
  cases H : x.gate <;> cases E : x.error <;> by_cases M : x.mobile=.empty <;>
    simp [fence,H,E,M] <;> split <;> simp

/-- Every mapped FENCE lane is active and has the same generated
displacement as the command occurrence, at the very same site. -/
theorem mapped_owner (g : LongGeometry) (j : Fin 11) (s : Sheet)
    (h : fenceSheet g j=some s) :
    activeSheet g s=true ∧ cmdDispl j=dataDispl s := by
  have J := j.isLt
  obtain ⟨j,hj⟩ := j
  dsimp only at J
  have E : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨
      j=8 ∨ j=9 ∨ j=10 := by omega
  rcases E with e|e|e|e|e|e|e|e|e|e|e <;> subst j <;>
    cases I : g.inside <;> simp_all [fenceSheet,activeSheet,cmdDispl,dataDispl] <;>
    subst s <;> exact ⟨rfl,rfl⟩

/-- FENCE cannot wait on a foreign or inactive lane. General old
word and modulus are accepted so this applies directly to an H6 chart. -/
theorem literal_blockade (g : Pair LongGeometry) (old : At Sheet → Lane)
    (a : At (Fin 11)) (p : Payload) (h : checkFence g old a p=.hold) :
    ∃ s, p.fault=0 ∧ p.opcode.toNat=11 ∧
      fenceSheet (geometry g a.side) a.occurrence=some s ∧
      activeSheet (geometry g a.side) s=true ∧
      (∀ m w, owner m w (cmdDispl a.occurrence)=owner m w (dataDispl s)) ∧
      (old ⟨a.side,s⟩).gate=true ∧ (old ⟨a.side,s⟩).error=false ∧
      (old ⟨a.side,s⟩).mobile≠.empty := by
  unfold checkFence at h
  split at h
  · contradiction
  · rename_i E
    have F : p.fault=0 ∧ p.opcode.toNat=11 := by simpa using E
    split at h
    · contradiction
    · rename_i s hs
      obtain ⟨A,D⟩ := mapped_owner _ _ _ hs
      exact ⟨s,F.1,F.2,hs,A,fun m w => congrArg (owner m w) D,(fence_hold_iff _ _).mp h⟩

#print axioms literal_blockade

/-- A bound healthy forward stopped by the race has a legal FIRST or
OTHER counter; malformed counters never remain as gate holds. -/
theorem race_wait (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK) (p : Payload) (old : bound g (readK x) a=.forward p)
    (wait : depart (geometry g a.side) a.occurrence p=none) :
    (p.fault==0 && gate p.opcode.toNat a.occurrence (geometry g a.side))=true ∧
      (p.race.toNat=1 ∨ p.race.toNat=2 ∨ p.race.toNat=3) := by
  unfold depart at wait
  split at wait
  · rename_i D
    dsimp only at wait
    split at wait
    · rename_i U
      suffices rL : 1≤p.race.toNat by exact ⟨D,by omega⟩
      have noFault : fault false ≠ .forward p := by
        intro H
        have E : p.fault=0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp D).1
        unfold fault at H
        cases H
        contradiction
      unfold bound at old
      generalize E : readK x a = tok at old
      cases tok with
      | empty => contradiction
      | trail => contradiction
      | reply q =>
        simp only [BStarLongCommand.bind] at old
        split at old
        · contradiction
        · split at old <;> contradiction
      | forward q =>
        let o := q.opcode.toNat
        let r := q.race.toNat
        let ok := if gate o a.occurrence (geometry g a.side) then decide (1≤r ∧ r≤5) else r==0
        change (if q.fault != 0 || decide (o≥413) || q.outcome != 0 || !ok
          then fault false else match forwardWidth o q.argument.toNat with
          | none => fault false
          | some w => .forward (cropped q w))=.forward p at old
        by_cases F : (q.fault != 0 || decide (o≥413) || q.outcome != 0 || !ok)=true
        · rw [if_pos F] at old
          exact (noFault old).elim
        · rw [if_neg F] at old
          split at old
          · exact (noFault old).elim
          · cases old
            have G := (Bool.and_eq_true_iff.mp D).2
            change gate o a.occurrence (geometry g a.side)=true at G
            have Z := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr F)).2
            have R : 1≤r ∧ r≤5 := by simpa [ok,G] using Z
            exact R.1
    · contradiction
  · contradiction

/-- First observation can be obtained at either end. After it, the
opposite physical incidence is nominated by its endpoint side. -/
theorem race_observation (g : LongGeometry) (j : Fin 11) (p : Payload)
    (gateOpen : (p.fault==0 && gate p.opcode.toNat j g)=true)
    (race : p.race.toNat=1 ∨ p.race.toNat=2 ∨ p.race.toNat=3) :
    ∃ side v, (p.race.toNat=2 → side=.left) ∧
      (p.race.toNat=3 → side=.right) ∧ observe ⟨side,j⟩ g p=some v := by
  rcases race with first|left|right
  · obtain ⟨v,H⟩ := BStarClearanceObserveJoined.nominate_other
      ⟨.left,j⟩ g p gateOpen (.inl first)
    exact ⟨.left,v,fun _ => rfl,by omega,H⟩
  · obtain ⟨v,H⟩ := BStarClearanceObserveJoined.nominate_other
      ⟨.left,j⟩ g p gateOpen (.inr (.inl ⟨rfl,left⟩))
    exact ⟨.left,v,fun _ => rfl,by omega,H⟩
  · obtain ⟨v,H⟩ := BStarClearanceObserveJoined.nominate_other
      ⟨.right,j⟩ g p gateOpen (.inr (.inr ⟨rfl,right⟩))
    exact ⟨.right,v,by omega,fun _ => rfl,H⟩

#print axioms race_wait
#print axioms race_observation

open BStarLongLiteral BStarLongWork BStarLongEvents

/-- The actual selected command either advances, waits for a race
observation at a specified incidence, or is blocked by an occupied
active lane of exactly its own generated owner. -/
theorem nominated_forward (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hm : c∈orderedCommands g) (nd : c.kind≠.door)
    (old : bound g (readK x) c.source=.forward p) :
    (∃ q, (c,.advance q)∈actualOffers g x) ∨
    ((c,.hold)∈actualOffers g x ∧
      (∃ side v, (p.race.toNat=2 → side=.left) ∧ (p.race.toNat=3 → side=.right) ∧
        observe ⟨side,c.source.occurrence⟩ (geometry g c.source.side) p=some v)) ∨
    ((c,.hold)∈actualOffers g x ∧
      ∃ s, fenceSheet (geometry g c.source.side) c.source.occurrence=some s ∧
        activeSheet (geometry g c.source.side) s=true ∧
        cmdDispl c.source.occurrence=dataDispl s ∧
        (BStarLongPrep.view x ⟨c.source.side,s⟩).gate=true ∧
        (BStarLongPrep.view x ⟨c.source.side,s⟩).error=false ∧
        (BStarLongPrep.view x ⟨c.source.side,s⟩).mobile≠.empty) := by
  classical
  have H := BStarSeparatorTags.forward_gated_hold_iff g x c p nd old
  by_cases T : gatedAt g x c=.hold
  · have M := BStarSeparatorTags.forward_hold_selected g x c p hm nd old (H.mp T)
    rcases H.mp T with r|⟨q,_,f⟩
    · have R := race_wait g x c.source p old r
      exact .inr (.inl ⟨M.1,race_observation _ _ _ R.1 R.2⟩)
    · obtain ⟨s,_,_,S,A,_,G,E,N⟩ := literal_blockade _ _ _ _ f
      exact .inr (.inr ⟨M.1,s,S,A,(mapped_owner _ _ _ S).2,G,E,N⟩)
  · have G : ∃ q, gatedAt g x c=.advance q := by
      unfold gatedAt classifyOld at *
      change checkOffer g (BStarLongPrep.view x)
        (c,classify c _ (bound g (readK x) c.source) _ )≠.hold at T
      change ∃ q, checkOffer g (BStarLongPrep.view x)
        (c,classify c _ (bound g (readK x) c.source) _)=.advance q
      rw [old] at T ⊢
      simp only [classify,beq_iff_eq,nd,if_false] at T ⊢
      cases E : depart (geometry g c.source.side) c.source.occurrence p with
      | none => simp [E,checkOffer] at T
      | some q =>
        cases F : checkFence g (BStarLongPrep.view x) c.source q
        · exact ⟨q,by simp [checkOffer,F]⟩
        · simp [E,checkOffer,F] at T
        · exact ⟨failedPayload,by simp [checkOffer,F]⟩
    obtain ⟨q,Q⟩ := G
    have m := (gated_mem g x c _).mpr ⟨hm,Q.symm⟩
    let d := round g x
    let v := cancel d.faults (c,.advance q)
    have V : v∈d.offered := List.mem_map.mpr ⟨_,m,rfl⟩
    let z := BStarLongGrant.update g x d.offered v
    have Z : z∈actualOffers g x := List.mem_map.mpr ⟨v,V,rfl⟩
    have P (u : Payload) : ∃ w, BStarLongGrant.update g x d.offered (c,.advance u)=(c,.advance w) := by
      unfold BStarLongGrant.update
      dsimp only
      split
      · split <;> exact ⟨_,rfl⟩
      · exact ⟨_,rfl⟩
    have E : ∃ u, v=(c,.advance u) := by
      unfold v cancel
      dsimp only
      split <;> exact ⟨_,rfl⟩
    obtain ⟨u,U⟩ := E
    obtain ⟨w,W⟩ := P u
    exact .inl ⟨w,(show z=(c,.advance w) by unfold z; rw [U,W]) ▸ Z⟩

#print axioms nominated_forward
end L4.BStarClearanceBlockade
