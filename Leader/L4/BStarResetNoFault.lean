import Leader.L4.BStarResetTaggedRows
import Leader.L4.BStarLongFenceTopology

namespace L4.BStarResetNoFault
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongCommandData BStarLongLiteral
open BStarLongPrep

-- All potentially selected prep lanes for one wire claim, without
-- depending on its old token or old data.
def potential (g : Pair LongGeometry) (c : CommandClaim) : List (At Sheet) :=
  if c.kind=.door then [] else
    (match c.source.occurrence.val with
    | 0 => [Sheet.ls]
    | 1 => if (geometry g c.source.side).inside then [Sheet.ld,Sheet.rd] else [Sheet.rd]
    | 2 => if (geometry g c.source.side).inside then [Sheet.rs] else []
    | 5 => if (geometry g c.source.side).inside then [Sheet.ls] else []
    | _ => []).map (fun s => ⟨c.source.side,s⟩)

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

theorem potential_nodup (g : Pair LongGeometry) :
    ((orderedCommands g).flatMap (potential g)).Nodup := by
  obtain ⟨x,y⟩ := g
  have A : orderedCommands (x,y)=orderedCommands (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
  have B : potential (x,y)=potential (geo false x.inside x.last,geo y.axes.h6 y.inside false) := by
    funext c
    have T : (geometry (x,y) c.source.side).inside = (geometry (geo false x.inside x.last,geo y.axes.h6 y.inside false) c.source.side).inside := by cases h : c.source.side <;> simp [geometry,geo]
    simp only [potential,T]
  rw [A,B]
  generalize x.inside=xi
  generalize x.last=xl
  generalize y.axes.h6=yh
  generalize y.inside=yi
  cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel

private theorem prep_subset (g : Pair LongGeometry) (c : CommandClaim)
    (op : Prep) (nd : c.kind≠.door) :
    ((prepSites (geometry g c.source.side) c.source.occurrence op).map (fun s => ⟨c.source.side,s⟩)).Sublist
      (potential g c) := by
  unfold potential
  rw [if_neg nd]
  apply List.Sublist.map
  generalize (geometry g c.source.side)=z
  generalize c.source.occurrence=j
  have E : ∀ j : Fin 11, (prepSites z j op).Sublist
      (match j.val with
      | 0 => [.ls]
      | 1 => if z.inside then [.ld,.rd] else [.rd]
      | 2 => if z.inside then [.rs] else []
      | 5 => if z.inside then [.ls] else []
      | _ => []) := by
    have T : ∀ j : Fin 11,
        prepSites z j op=prepSites (geo false z.inside false) j op := by
      intro j
      cases op <;> rfl
    simp only [T]
    generalize z.inside=zi
    cases zi <;> cases op <;> decide +kernel
  exact E j

private def contribution (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) : List BStarLongPrep.Offer :=
  match gatedAt g x c with
  | .advance p => fieldOffers g x c.source p
  | _ => []

private theorem contribution_subset (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) :
    ((contribution g x c).map (fun o => o.claim.lane)).Sublist (potential g c) := by
  unfold contribution
  split
  all_goals try exact List.nil_sublist _
  rename_i p h
  have nd : c.kind≠.door := by
    intro D
    simp [gatedAt,classifyOld,classify,D,checkOffer] at h
  unfold fieldOffers
  split
  · exact List.nil_sublist _
  split
  · exact List.nil_sublist _
  rename_i op hOp
  simp only [prepClaims,List.map_map,Function.comp_def]
  exact prep_subset g c op nd

private theorem contributions (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (round g x).prep=(orderedCommands g).flatMap (contribution g x) := by
  unfold round gated offersOn preparedBy
  simp only [List.map_map,List.flatMap_map,Function.comp_def]
  rfl

theorem prep_lanes_nodup (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (((round g x).prep).map (fun a => a.claim.lane)).Nodup := by
  rw [contributions,List.map_flatMap]
  have H (l : List CommandClaim) :
      (l.flatMap (fun c => (contribution g x c).map (fun a => a.claim.lane))).Sublist
        (l.flatMap (potential g)) := by
    induction l with
    | nil => exact List.Sublist.slnil
    | cons c l ih =>
      simp only [List.flatMap_cons]
      exact (contribution_subset g x c).append ih
  exact (potential_nodup g).sublist (H _)

private theorem insert_perm {α : Type} (key : α → Nat) (a : α) (xs : List α) :
    (BStarLongClaims.insert key a xs).Perm (a::xs) := by
  induction xs with
  | nil => exact .refl _
  | cons b l ih =>
    unfold BStarLongClaims.insert
    split
    · exact .refl _
    · exact (List.Perm.cons b ih).trans (List.Perm.swap a b l)

private theorem offers_perm {α : Type} (key : α → Nat) (xs : List α) :
    (offers key xs).Perm xs := by
  induction xs with
  | nil => exact .refl _
  | cons a l ih =>
    exact (insert_perm key a (offers key l)).trans (.cons a ih)

private theorem all_win (used : List (At Sheet)) (xs : List BStarLongPrep.Offer)
    (H : (xs.map (fun a => a.claim.lane) ++ used).Nodup) :
    arbitrate used xs=(xs,[]) := by
  induction xs generalizing used with
  | nil => rfl
  | cons a l ih =>
    have Hand := List.nodup_cons.mp (show
      (a.claim.lane::(l.map (fun a => a.claim.lane) ++ used)).Nodup from H)
    have hf : free used [a.claim.lane]=true := (free_iff ..).mpr (by
      intro s hs
      have E := List.mem_singleton.mp hs
      subst s
      exact fun bad => Hand.1 (List.mem_append.mpr (.inr bad)))
    have H' : (l.map (fun a => a.claim.lane) ++ a.claim.lane::used).Nodup := by
      rw [List.nodup_append]
      refine ⟨?_,?_,?_⟩
      · exact (List.nodup_append.mp Hand.2).1
      · exact List.nodup_cons.mpr ⟨fun bad => Hand.1 (List.mem_append.mpr (.inr bad)),
          (List.nodup_append.mp Hand.2).2.1⟩
      · intro s hs t ht eq
        subst t
        rcases List.mem_cons.mp ht with rfl|ht
        · exact Hand.1 (List.mem_append.mpr (.inl hs))
        · exact (List.nodup_append.mp Hand.2).2.2 _ hs _ ht rfl
    simp only [arbitrate,hf,if_true,ih _ H']

theorem arb_no_losers (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (arbitration (round g x).prep).2=[] := by
  unfold arbitration
  rw [all_win]
  simpa only [List.append_nil] using ((offers_perm offerPriority
    (round g x).prep).map (fun (a : BStarLongPrep.Offer) => a.claim.lane)).nodup_iff.mpr
      (prep_lanes_nodup g x)

theorem origin_unique (g : Pair LongGeometry) (C D : CommandClaim)
    (hc : C∈orderedCommands g) (hd : D∈orderedCommands g)
    (hs : C.source=D.source) : C=D := by
  have H : (orderedCommands g).all (fun c => (orderedCommands g).all
      (fun d => c.source != d.source || c==d)) =true := by
    clear hc hd hs
    obtain ⟨x,y⟩ := g
    have E : orderedCommands (x,y)=orderedCommands (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
    rw [E]
    generalize x.inside=xi
    generalize x.last=xl
    generalize y.axes.h6=yh
    generalize y.inside=yi
    cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel
  exact beq_iff_eq.mp (by simpa [hs] using List.all_eq_true.mp (List.all_eq_true.mp H C hc) D hd)

open BStarResetTaggedRows

/-- On the literal pair, op0/1/2 may start on entirely arbitrary
command/data bytes. No reset-origin preparation can be cancelled. -/
theorem reset_no_prep_fault (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (op : Nat) (hop : op=0 ∨ op=1 ∨ op=2)
    (hC : (C,.advance (resetPayload op))∈gated g x) :
    C.source∉(round g x).faults := by
  intro faulted
  change C.source∈prepFaults (view x) (round g x).prep at faulted
  have fm : (arbitration (round g x).prep).2=[] := arb_no_losers g x
  simp only [prepFaults,fm,List.map_nil,List.nil_append] at faulted
  obtain ⟨o,hom,he⟩ := List.mem_map.mp faulted
  obtain ⟨win,ofault⟩ := List.mem_filter.mp hom
  have oi : o∈(round g x).prep := by
    unfold arbitration at win
    rw [arbitrate_winners] at win
    exact (offers_perm offerPriority _).mem_iff.mp ((select_sublist ..).subset win)
  change o∈preparedBy g x (gated g x) at oi
  unfold preparedBy at oi
  obtain ⟨⟨D,act⟩,hd,oi⟩ := List.mem_flatMap.mp oi
  cases act <;> try (exact False.elim (List.not_mem_nil oi))
  rename_i q
  change o∈fieldOffers g x D.source q at oi
  have structure_of_offer : ∃ prep s, prepOf q.opcode.toNat=some prep ∧
      o=⟨⟨prep,D.source,⟨D.source.side,s⟩⟩,
        if prep==.load then loadPayload x ⟨D.source.side,s⟩ q else .empty⟩ := by
    unfold fieldOffers at oi
    split at oi
    · contradiction
    split at oi
    · contradiction
    rename_i prep pre
    obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp oi
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hcl
    exact ⟨prep,s,pre,rfl⟩
  obtain ⟨prep,s,pre,hshape⟩ := structure_of_offer
  have hs : D.source=C.source := by simpa [hshape] using he
  obtain ⟨mc,H⟩ := (gated_mem g x C _).mp hC
  obtain ⟨md,Q⟩ := (gated_mem g x D _).mp hd
  have E := origin_unique g D C md mc hs
  subst D
  have J := Q.trans H.symm
  injection J with J
  subst q
  cases hop with
  | inl h =>
    subst op
    have e : prep=.rstop := Option.some.inj (by exact pre.symm)
    subst prep
    simp [hshape,selectedEffects,effects] at ofault
  | inr h =>
    rcases h with h|h <;> subst op
    · have e : prep=.rclear := Option.some.inj (by exact pre.symm)
      subst prep
      simp [hshape,selectedEffects,effects] at ofault
    · contradiction

theorem healthy (op : Nat) (h : op=0 ∨ op=1 ∨ op=2) : ResetF (resetPayload op) := by
  rcases h with rfl|rfl|rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))

theorem joined_link_no_fault (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (op : Nat) (hop : op=0 ∨ op=1 ∨ op=2) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.destination=some d →
    readK raw C.source=.forward (resetPayload op) →
    readK out C.source=.trail ∧ readK out d=.forward (resetPayload op) := by
  dsimp only
  intro hc hd hsrc
  have H := reset_link_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C d (resetPayload op)
  have E := H hc hd hsrc (healthy op hop)
  have S := (BStarAcquireReturn.link_shape _ _ _ hc hd).2.1
  have nf := reset_no_prep_fault _ _ C op hop
    (gated_reset _ _ _ _ hc (by simp [S]) hsrc (healthy op hop))
  exact ⟨E.1, E.2.trans (congrArg Token.forward (if_neg nf))⟩

theorem joined_terminal_no_fault (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (op : Nat) (hop : op=0 ∨ op=1 ∨ op=2) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let out := Pair.map LargeSite.long (largePair b x)
    C∈orderedCommands g → C.kind=.terminal → C.destination=none →
    C.source.occurrence.val=10 → readK raw C.source=.forward (resetPayload op) →
    readK out C.source=.reply (resetPayload op) := by
  dsimp only
  intro hc ht hd h10 hsrc
  have H := reset_terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C (resetPayload op)
  have E := H hc ht hd h10 hsrc (healthy op hop)
  have nf := reset_no_prep_fault _ _ C op hop
    (gated_reset _ _ _ _ hc (by simp [ht]) hsrc (healthy op hop))
  refine (E.trans (congrArg finish (if_neg nf))).trans ?_
  rcases hop with rfl|rfl|rfl <;> rfl

end L4.BStarResetNoFault
