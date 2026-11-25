import Leader.L4.BStarLongGrantProjection

/-! A release request has a literal old occurrence as witness. This does not
authenticate that occurrence's owner or the issue time. -/
namespace L4.BStarReleaseOrigin
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongGrant
open BStarLongWork BStarLongGrantProjection

def HealthyOp (op : Nat) (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=op

abbrev Effective := HealthyOp releaseOp

theorem ungated (g : LongGeometry) (j : Fin 11) (p : Payload) (h : Effective p) :
    gate p.opcode.toNat j g=false := by
  rw [h.2]
  simp [gate,releaseOp,admit,bitOp]

theorem classify_origin_ungated (c : CommandClaim) (g : LongGeometry) (u v : Token)
    (p : Payload) (h : gate p.opcode.toNat c.source.occurrence g=false)
    (H : classify c g u v=.advance p) :
    u=.forward p := by
  unfold classify at H
  split at H
  · contradiction
  cases u with
  | forward q =>
    change (match depart g c.source.occurrence q with
      | none => Offer.hold
      | some t => Offer.advance t) = Offer.advance p at H
    have D : depart g c.source.occurrence q=some p := by
      cases E : depart g c.source.occurrence q <;> simp_all
    unfold depart at D
    dsimp only at D
    split at D
    · rename_i hr
      split at D
      · contradiction
      · have P := Option.some.inj D
        have O := congrArg (fun a : Payload => a.opcode.toNat) P
        change q.opcode.toNat=p.opcode.toNat at O
        rw [O,h, Bool.and_false] at hr
        contradiction
    · exact congrArg Token.forward (Option.some.inj D)
  | empty | trail | reply =>
    split at H
    · split at H <;> contradiction
    · cases v <;> (try contradiction) <;> split at H <;> contradiction

theorem classify_origin (c : CommandClaim) (g : LongGeometry) (u v : Token)
    (p : Payload) (h : Effective p) (H : classify c g u v=.advance p) :
    u=.forward p :=
  classify_origin_ungated c g u v p (ungated g c.source.occurrence p h) H

theorem crop_origin_op (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (op : Nat) (h : HealthyOp op p) (H : bind g j t=.forward p) :
    ∃ q, t=.forward q ∧ HealthyOp op q := by
  cases t with
  | empty | trail => contradiction
  | reply q =>
    simp only [BStarLongCommand.bind] at H
    split at H
    · contradiction
    · split at H <;> contradiction
  | forward q =>
    have z : (fault false : Token)≠.forward p := by
      intro eq
      have e := congrArg Payload.fault (Token.forward.inj eq)
      simp [h.1] at e
    simp only [BStarLongCommand.bind] at H
    split at H <;> (
      split at H
      · contradiction
      · split at H
        · contradiction
        · have E := Token.forward.inj H
          exact ⟨q,rfl,(congrArg Payload.fault E).trans h.1,
            (congrArg (fun a : Payload => a.opcode.toNat) E).trans h.2⟩)

theorem crop_origin (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (h : Effective p) (H : bind g j t=.forward p) :
    ∃ q, t=.forward q ∧ Effective q :=
  crop_origin_op g j t p releaseOp h H

theorem pre_grant_ungated_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3) (op : Nat) (hg : ∀ g i, gate op i g=false)
    (H : requested (round g x).offered s j op=true) :
    ∃ c p q, c∈orderedCommands g ∧ c.source.side=s ∧ c.source.occurrence.val=j.val ∧
      (c,.advance p)∈(round g x).offered ∧ HealthyOp op p ∧
      oldTokens x c.source=.forward q ∧ HealthyOp op q := by
  obtain ⟨⟨c,t⟩,ht,hh⟩ := List.any_eq_true.mp H
  simp only [Bool.and_eq_true,beq_iff_eq] at hh
  obtain ⟨⟨hs,hj⟩,hh⟩ := hh
  cases t <;> simp at hh
  rename_i p
  obtain ⟨hf,ho⟩ := hh
  have hp : HealthyOp op p := ⟨hf,ho⟩
  have hw : Offer.advance failedPayload≠Offer.advance p := by
    intro eq
    have E := Offer.advance.inj eq
    have W := congrArg Payload.fault E
    simp [failedPayload,hf] at W
  have H' := ht
  change (c,.advance p)∈(gated g x).map (cancel (round g x).faults) at H'
  obtain ⟨⟨c',t'⟩,hm,he⟩ := List.mem_map.mp H'
  cases t' <;> simp [cancel] at he
  rename_i p'
  obtain hfirst : c'=c := by split at he <;> exact (Prod.mk.inj he).1
  subst c'
  have E : p'=p := by
    split at he
    · exact (hw (congrArg Prod.snd he)).elim
    · exact Offer.advance.inj (congrArg Prod.snd he)
  subst p'
  change (c,.advance p)∈(offersOn g (oldTokens x)).map
    (fun m => (m.1,checkOffer g (BStarLongPrep.view x) m)) at hm
  obtain ⟨⟨d,a⟩,hm,he⟩ := List.mem_map.mp hm
  have E : d=c := (Prod.mk.inj he).1
  subst d
  have K : checkOffer g (BStarLongPrep.view x) (c,a)=.advance p := (Prod.mk.inj he).2
  have A : a=.advance p := by
    cases a <;> simp [checkOffer] at K
    rename_i v
    cases e : checkFence g (BStarLongPrep.view x) c.source v <;>
      simp [e] at K
    · exact congrArg Offer.advance K
    · exact (hw (congrArg Offer.advance K)).elim
  subst a
  unfold offersOn at hm
  obtain ⟨d,dm,de⟩ := List.mem_map.mp hm
  have E : d=c := (Prod.mk.inj de).1
  subst d
  have D := classify_origin_ungated c _ _ _ p (by rw [ho]; exact hg _ _) (Prod.mk.inj de).2
  obtain ⟨q,hq,htq⟩ := crop_origin_op _ _ _ _ op hp D
  exact ⟨c,p,q,dm,hs,hj,ht,hp,hq,htq⟩

theorem pre_grant_release_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3)
    (H : requested (round g x).offered s j releaseOp=true) :
    ∃ c p q, c∈orderedCommands g ∧ c.source.side=s ∧ c.source.occurrence.val=j.val ∧
      (c,.advance p)∈(round g x).offered ∧ Effective p ∧
      oldTokens x c.source=.forward q ∧ Effective q :=
  pre_grant_ungated_origin g x s j releaseOp
    (fun g i => by simp [gate,releaseOp,admit,bitOp]) H

theorem pre_grant_acquire_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3)
    (H : requested (round g x).offered s j acquire=true) :
    ∃ c p q, c∈orderedCommands g ∧ c.source.side=s ∧ c.source.occurrence.val=j.val ∧
      (c,.advance p)∈(round g x).offered ∧ HealthyOp acquire p ∧
      oldTokens x c.source=.forward q ∧ HealthyOp acquire q :=
  pre_grant_ungated_origin g x s j acquire
    (fun g i => by simp [gate,acquire,admit,bitOp]) H

#print axioms pre_grant_acquire_origin

/-- If the old physical incidence does not contain a nonfaulting RREL
front, the actual joined mark cannot clear its canonical header grant.
A history theorem must still show which process placed such a front. -/
theorem joined_keep_without_old_release (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (geometry g s).axes.h6=true →
    canonical (original (BStarLongGrant.atOld raw s)) j=true →
    (∀ q, oldTokens raw ⟨s,⟨j.val,by have := j.isLt; omega⟩⟩=.forward q → ¬ Effective q) →
    read (Pair.map LargeSite.long (largePair b x)) s j=1 := by
  dsimp only
  intro hh hc hn
  apply joined_keeps_incidence _ _ _ _ _ _ _ _ _ hp x s j hh hc
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨claim,_,q,_,hs,hj,_,_,hq,he⟩ :=
    pre_grant_release_origin _ _ s j h
  have H : claim.source=⟨s,⟨j.val,by have := j.isLt; omega⟩⟩ := by
    have H' : claim.source.occurrence=⟨j.val,by have := j.isLt; omega⟩ := Fin.ext hj
    cases E : claim.source
    simp only [E] at hs H'
    simp [hs,H']
  exact hn q (H ▸ hq) he

#print axioms pre_grant_release_origin
#print axioms joined_keep_without_old_release
end L4.BStarReleaseOrigin
