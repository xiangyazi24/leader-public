import Leader.L4.BStarLongEvents

/-! Exact inherited-or-generated COMMIT event in terms of the
initiator's immutable old packed word (not a downstream offer). -/
namespace L4.BStarLongLiteral
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongEvents BStarLongWork BStarLongCommandData

def centerLink (g : Pair LongGeometry) : CommandClaim :=
  link (L 1) (R (if g.2.axes.h6 then 2 else 1))

theorem center_mem (g : Pair LongGeometry) : centerLink g∈orderedCommands g := by
  have h : centerLink g∈(orderedCommands g).filter centerClaim := by
    rw [one_center_claim]; simp [centerLink]
  exact (List.mem_filter.mp h).1

theorem center_of (g : Pair LongGeometry) (c : CommandClaim)
    (hm : c∈orderedCommands g) (hj : c.source.occurrence.val=1) : c=centerLink g := by
  have h : c∈(orderedCommands g).filter centerClaim := List.mem_filter.mpr ⟨hm,by simp [centerClaim,hj]⟩
  rw [one_center_claim] at h
  exact List.mem_singleton.mp h

def classifyOld (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) :
    BStarLongCommand.Offer :=
  let read := fun a => bind (geometry g a.side) a.occurrence (oldTokens x a)
  classify c (geometry g c.source.side) (read c.source)
    ((c.destination.map read).getD .empty)

def gatedAt (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim) :
    BStarLongCommand.Offer :=
  checkOffer g (BStarLongPrep.view x) (c,classifyOld g x c)

theorem gated_mem (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim)
    (q : BStarLongCommand.Offer) :
    (c,q)∈gated g x ↔ c∈orderedCommands g ∧ q=gatedAt g x c := by
  unfold gated offersOn
  simp only [List.map_map,Function.comp_def,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨a,hm,rfl,h⟩
    exact ⟨hm,h.symm⟩
  · rintro ⟨hm,rfl⟩
    exact ⟨c,hm,rfl,rfl⟩

private theorem sort_mem {C : Type} (key : C → Nat) (a : C) (xs : List C) :
    a∈offers key xs → a∈xs := by
  have ins (q : C) (tail : List C) : a∈BStarLongClaims.insert key q tail → a=q ∨ a∈tail := by
    induction tail with
    | nil => simp [BStarLongClaims.insert]
    | cons b bs ih =>
      unfold BStarLongClaims.insert
      split
      · simp
      · simp only [List.mem_cons]
        intro H
        rcases H with h|h
        · exact .inr (.inl h)
        · rcases ih h with qeq|bt
          · exact .inl qeq
          · exact .inr (.inr bt)
  induction xs with
  | nil => simp [offers]
  | cons q qs ih =>
    intro h
    change a∈BStarLongClaims.insert key q (offers key qs) at h
    exact List.mem_cons.mpr ((ins q _ h).imp_right ih)

private theorem fault_origin (old : At Sheet → BStarLongPackets.Lane)
    (ps : List BStarLongPrep.Offer) (a : At (Fin 11))
    (h : a∈BStarLongPrep.prepFaults old ps) :
    ∃ p∈ps, p.claim.origin=a := by
  unfold BStarLongPrep.prepFaults at h
  rcases List.mem_append.mp h with l|w
  · obtain ⟨q,m,rfl⟩ := List.mem_map.mp l
    exact ⟨q,sort_mem _ _ _ ((BStarLongPrep.arbitrate_losers [] _).subset m),rfl⟩
  · obtain ⟨q,m,rfl⟩ := List.mem_map.mp w
    rw [BStarLongPrep.arbitration,BStarLongPrep.arbitrate_winners] at m
    exact ⟨q,sort_mem _ _ _ ((select_sublist ..).subset (List.mem_filter.mp m).1),rfl⟩

private theorem prep_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : At (Fin 11))
    (p : Payload) (q : BStarLongPrep.Offer) (h : q∈fieldOffers g x a p) :
    q.claim.origin=a := by
  unfold fieldOffers at h
  split at h
  · simp at h
  split at h
  · simp at h
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hb
    rfl

private theorem commit_escapes_prep (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (h : gatedAt g x (centerLink g)=.advance p)
    (hop : p.opcode.toNat=commitOp) :
    L 1∉(round g x).faults := by
  intro bad
  obtain ⟨a,ha,orig⟩ := fault_origin _ _ _ bad
  obtain ⟨⟨c,o⟩,hc,H⟩ := List.mem_flatMap.mp ha
  cases o <;> try (simp at H)
  rename_i q
  change a∈fieldOffers g x c.source q at H
  have E := (prep_origin g x c.source q a H).symm.trans orig
  obtain ⟨cm,hq⟩ := (gated_mem g x c (.advance q)).mp hc
  have cEq := center_of g c cm (congrArg (fun z : At (Fin 11) => z.occurrence.val) E)
  subst c
  rw [h] at hq
  injection hq with qEq
  subst q
  simp [fieldOffers,hop,commitOp,prepOf] at H

private theorem grant_preserves_commit (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (c : CommandClaim) (o : BStarLongCommand.Offer) (p : Payload)
    (hop : p.opcode.toNat=commitOp) :
    BStarLongGrant.update g x os (c,o)=(c,.advance p) ↔ o=.advance p := by
  have no (q : Payload) (j : Fin 3) (b : Bool)
      (h : q.opcode.toNat=acquire) : BStarLongGrant.capture (atOld x c.source) j q b≠p := by
    intro E
    have C := congrArg (fun r : Payload => r.opcode.toNat) E
    cases b <;> simp [BStarLongGrant.capture,BStarLongGrant.captureFields,h,hop,acquire,commitOp] at C
  by_cases h3 : c.source.occurrence.val<3
  · cases o <;> simp [BStarLongGrant.update,h3]
    rename_i q
    split
    · rename_i h
      have k : q.opcode.toNat=acquire := h.2
      have neq : q≠p := by intro E; subst q; simp [hop,acquire,commitOp] at k
      simpa [neq, BStarLongGrant.atOld, atOld] using
        no q ⟨c.source.occurrence.val,h3⟩
          (BStarLongGrant.win
            (BStarLongGrant.original (BStarLongGrant.atOld x c.source.side))
            (fun a => BStarLongGrant.requested os c.source.side a BStarLongGrant.releaseOp)
            (fun a => BStarLongGrant.requested os c.source.side a acquire)
            ⟨c.source.occurrence.val,h3⟩) k
    · simp
  · simp [BStarLongGrant.update,h3]

private theorem uncancel (fs : List (At (Fin 11))) (c d : CommandClaim)
    (o : BStarLongCommand.Offer) (p : Payload) (hop : p.opcode.toNat=commitOp)
    (H : cancel fs (c,o)=(d,.advance p)) :
    (c,o)=(d,.advance p) := by
  cases o <;> try (exact H)
  by_cases m : c.source∈fs
  · have E : failedPayload=p := by simpa [cancel,m] using congrArg Prod.snd H
    have K := congrArg (fun r : Payload => r.opcode.toNat) E
    simp [failedPayload,hop,commitOp] at K
  · simpa [cancel,m] using H

private theorem actual_center_commit (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (hop : p.opcode.toNat=commitOp) :
    (centerLink g,.advance p)∈actualOffers g x ↔ gatedAt g x (centerLink g)=.advance p := by
  let d := round g x
  let c := centerLink g
  change (c,.advance p)∈d.offered.map (BStarLongGrant.update g x d.offered) ↔ _
  constructor
  · intro hm
    obtain ⟨⟨c',o⟩,hm,he⟩ := List.mem_map.mp hm
    have ec : c'=c := (update_claim g x d.offered (c',o)).symm.trans (congrArg Prod.fst he)
    subst c'
    have oh := (grant_preserves_commit g x d.offered c o p hop).mp he
    subst o
    obtain ⟨⟨b,q⟩,hb,be⟩ := List.mem_map.mp hm
    have E := uncancel _ b c q p hop be
    rw [E] at hb
    exact ((gated_mem g x c (.advance p)).mp hb).2.symm
  · intro hg
    have hf : c.source∉d.faults := commit_escapes_prep g x p hg hop
    have hg' := (gated_mem g x c (.advance p)).mpr ⟨center_mem g,hg.symm⟩
    have he : cancel d.faults (c,Offer.advance p)=(c,Offer.advance p) := by
      change (if c.source∈d.faults then (c,Offer.advance failedPayload) else (c,Offer.advance p))=_
      rw [if_neg hf]
    have hd : (c,.advance p)∈d.offered := List.mem_map.mpr ⟨(c,.advance p),hg',he⟩
    exact List.mem_map.mpr ⟨(c,.advance p),hd,
      (grant_preserves_commit g x d.offered c (.advance p) p hop).mpr rfl⟩

private theorem gated_center_commit (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (hop : p.opcode.toNat=commitOp) :
    gatedAt g x (centerLink g)=.advance p ↔
      bind g.1 1 (atSite x.1 1)=.forward p := by
  have n (q : Payload) (h : q.opcode.toNat=commitOp) :
      depart g.1 1 q=some q := by
    simp [depart,gate,h,commitOp,admit,bitOp]
  have check (o : BStarLongCommand.Offer) :
      checkOffer g (BStarLongPrep.view x) (centerLink g,o)=o := by
    cases o <;> try rfl
    rename_i q
    have f : checkFence g (BStarLongPrep.view x) (L 1) q=.advance := by
      unfold checkFence
      split
      · rfl
      · rfl
    simp only [checkOffer,show (centerLink g).source=L 1 by rfl,f]
  have localrow (t u : Token) :
      classify (centerLink g) g.1 t u=.advance p ↔ t=.forward p := by
    cases t with
    | empty | trail | reply _ => cases u <;> simp [classify,centerLink,link]
    | forward q =>
      simp only [classify,centerLink,link,L]
      change (match depart g.1 1 q with | none => Offer.hold | some v => Offer.advance v) =
        Offer.advance p ↔ Token.forward q=Token.forward p
      cases D : depart g.1 1 q with
      | none =>
        have N : q≠p := by
          intro eq
          subst q
          rw [n p hop] at D
          contradiction
        simp [N]
      | some v =>
        have opc : v.opcode=q.opcode := by
          unfold depart at D
          split at D
          · dsimp only at D
            split at D
            · contradiction
            · injection D with E
              rw [←E]
          · simp_all
        simp only [BStarLongCommand.Offer.advance.injEq,Token.forward.injEq]
        constructor
        · intro E
          have Q : q.opcode.toNat=commitOp := by rw [←opc,E,hop]
          rw [n q Q] at D
          simpa [E] using D
        · intro E
          subst q
          simpa [n p hop] using D.symm
  unfold gatedAt
  rw [check]
  exact localrow _ _

/-- Unconditional literal publication, in terms of the original raw
word and old geometry. No genesis, unique-owner, or reset hypothesis. -/
theorem raw_literal_commit_iff (g : Pair LongGeometry) (x : Pair (BitVec LW)) (e : Publication) :
    e∈(longTrace g x).publications ↔
      e.endpoint=.left ∧ ∃ p, bind g.1 1 (atSite x.1 1)=.forward p ∧
        LiteralCommit g.1 (L 1) x.1 p e.bank := by
  rw [literal_event_iff]
  constructor
  · rintro ⟨c,p,hm,he,H⟩
    have cm : c∈(actualOffers g x).map Prod.fst := List.mem_map.mpr ⟨(c,.advance p),hm,rfl⟩
    rw [actualOffers_claims] at cm
    have E := center_of g c cm H.1
    subst c
    have O : p.opcode.toNat=commitOp := H.2.2.2.1
    refine ⟨he,p,(gated_center_commit g x p O).mp ((actual_center_commit g x p O).mp hm),H⟩
  · rintro ⟨he,p,h,hc⟩
    have O := hc.2.2.2.1
    exact ⟨centerLink g,p,(actual_center_commit g x p O).mpr
      ((gated_center_commit g x p O).mpr h),he,hc⟩

#print axioms raw_literal_commit_iff
end L4.BStarLongLiteral
