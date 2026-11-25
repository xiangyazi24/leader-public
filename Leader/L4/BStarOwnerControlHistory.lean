import Leader.L4.BStarClearanceResidual
import Leader.L4.BStarDirtyReplySweep

namespace L4.BStarOwnerControlHistory
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarAcquireForwardTrace BStarLongFixedRouting BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarResetSchedule
open BStarSeparatingRail BStarResetQuiet BStarResetQuietTable BStarResetIdleRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem address_inj (e : Fin n) (he : e≠rightNeighbor e)
    (a b : AtK) (E : address e a=address e b) : a=b := by
  rcases a with ⟨s,i⟩
  rcases b with ⟨t,j⟩
  have J := congrArg Prod.snd E
  change i=j at J
  subst j
  have H := congrArg Prod.fst E
  cases s <;> cases t <;> first | rfl | exact (he H).elim | exact (he H.symm).elim

/-- On every mark an old completely empty owner rail keeps its
strict suffix empty. Old ISSUE can affect the root, but cannot feed a
selected forward link on that mark. -/
theorem empty_away_from_door {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
    (e : Fin n) (he : e≠rightNeighbor e) :
    ∀ j, (0<j ∨ e≠RearTrace.predecessor (S.getD 0 fallback).1) → j≤len →
      project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e) j=.empty := by
  intro j hj hlen
  let addr := fun j => S.getD j fallback
  let U := project addr x
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have read (j : Nat) (a : AtK) (H : addr j=address e a) : readK raw a=U j :=
    (old_read x e a).trans ((congrArg (atCursor x) H).symm)
  have Eread (j : Nat) (a : AtK) (H : addr j=address e a) (hl : j≤len) :
      bound g (readK raw) a=.empty := by
    have E := (read j a H).trans (clean j hl)
    exact (quiet_bound g (readK raw) a (.inl E)).trans E
  have links (i : Nat) (Lh : linkAt hp x e addr len i) :
      ∃ (a b : AtK), addr i=address e a ∧ addr (i+1)=address e b ∧
        avoids a (middle g raw) ∧ avoids b (middle g raw) := by
    obtain ⟨hi,K,d,hK,hd,hs,ht⟩ := Lh
    have ht' := Eread (i+1) d ht (by omega)
    have H : LinkHold (bound g (readK raw) K.source) (bound g (readK raw) d) := by
      rw [Eread i K.source hs (by omega),ht']
      exact .ee
    exact ⟨K.source,d,hs,ht,link_avoids g raw K d hK
      (BStarAcquireReturn.link_shape g K d hK hd).2.1 hd H⟩
  have selected (a : AtK) (H : addr j=address e a) :
      project addr (AllSizeS1Geometry.step B x e) j=.empty := by
    have hn := not_discarded hp C same e j hlen a H
    have hR : ¬(a=R 0 ∧ g.2.axes.h6=true) := by
      rintro ⟨rfl,head⟩
      have hOld : oldH6 B base (rightNeighbor e)=true :=
        (congrArg Prod.fst (same (rightNeighbor e))).trans head
      have L := C.length
      have M : addr j∈S := by
        change S.getD j fallback∈S
        rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
        exact List.getElem_mem _
      have Own := (C.entries _ M).2
      rw [H] at Own
      have atRoot := (endpoint_spec _ hh o 0).2.2 (rightNeighbor e) hOld Own
      have eq : addr j=addr 0 := H.trans (atRoot.trans C.root.symm)
      have J := (List.getD_inj (by omega) (by omega) C.nodup).mp eq
      rcases hj with pos|away
      · omega
      · apply away
        have eqSite : rightNeighbor e=(addr 0).1 :=
          (congrArg Prod.fst H).symm.trans (congrArg Prod.fst eq)
        exact (RearTrace.predecessor_right e).symm.trans
          (congrArg RearTrace.predecessor eqSite)
    have safe : DoorSafe g raw a := by
      by_cases A : a=R 0
      · subst a
        refine ⟨fun _ hh => (hR ⟨rfl,hh⟩).elim,?_⟩
        intro _ cl k hcl _
        have eq := (BStarK0Frame.door_eq g raw cl k hcl).1
        have M : cl∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨(cl,.door k),hcl,rfl⟩
        have hh := (BStarResetChartIndex.selected_door g cl M (eq ▸ rfl)).2.1
        exact (hR ⟨rfl,hh⟩).elim
      · exact safe_nonright _ _ _ A
    have hm : avoids a (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mc : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      have K := touches hp C same e j hlen v.1 a mc ha H
      have G : avoids a (middle g raw) := by
        rcases K with ⟨_,dk,da⟩|⟨J,T⟩|L|⟨i,I,L⟩
        · exact (hR ⟨da,(BStarResetChartIndex.selected_door g v.1 mc dk).2.1⟩).elim
        · subst j
          obtain ⟨K,M,hk,_,_,S⟩ := T
          have A := address_inj e he a K.source (H.symm.trans S)
          subst a
          exact terminal_avoids g raw K M hk (by rw [Eread len K.source H hlen]; exact .e)
        · obtain ⟨b,d,HB,_,hb,_⟩ := links j L
          exact (address_inj e he a b (H.symm.trans HB)).symm ▸ hb
        · obtain ⟨b,d,_,D,_,hd⟩ := links i L
          have eq : addr j=address e d := I ▸ D
          exact (address_inj e he a d (H.symm.trans eq)).symm ▸ hd
      intro w hw
      exact G w (List.mem_flatMap.mpr ⟨v,hv,hw⟩)
    have R := idle_at hp x e he a (.inl (.inl ((read j a H).trans (clean j hlen)))) hn hm safe
    exact (congrArg (atCursor (AllSizeS1Geometry.step B x e)) H).trans
      (R.trans ((congrArg (atCursor x) H).symm.trans (clean j hlen)))
  by_cases hl : (addr j).1=e
  · exact selected (L (addr j).2) (Prod.ext hl rfl)
  · by_cases hr : (addr j).1=rightNeighbor e
    · exact selected (R (addr j).2) (Prod.ext hr rfl)
    · exact (idle_off_pair hp x e (addr j) hl hr).trans (clean j hlen)



open BStarClearanceSource BStarClearanceResidual BStarResetControllerEntry
open BStarSeparatorControl BStarAcquireWaitControl

theorem idle_nonown {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
    (e : Fin n) (he : e≠rightNeighbor e)
    (away : e≠RearTrace.predecessor (S.getD 0 fallback).1) :
    let addr := fun j => S.getD j fallback
    let root := (addr 0).1
    let y := AllSizeS1Geometry.step B x e
    (∀ j≤len, project addr y j=.empty) ∧ control (y root).long=control (x root).long := by
  dsimp only
  refine ⟨fun j hj => empty_away_from_door hp C same clean e he j (.inr away) hj,?_⟩
  let root := (S.getD 0 fallback).1
  have R : root≠rightNeighbor e := fun r => away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor r.symm))
  by_cases E : root=e
  · have head := (root_header hp C same).1
    change oldH6 B x root=true at head
    rw [E] at head
    rw [show (AllSizeS1Geometry.step B x e root).long=(largePair B (x e,x (rightNeighbor e))).1.long by
      simp only [AllSizeS1Geometry.step,E,if_true]]
    exact (BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) head).trans (congrArg (fun i : Fin n => control (x i).long) E.symm)
  · simp only [AllSizeS1Geometry.step,if_neg E,if_neg R,root]

/-- A clean legal owner can only issue by selecting its own incoming
mark. Foreign marks preserve the exact program counter and every slot. -/
theorem idle_launch_or_hold {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e) (e : Fin n) :
    let addr := fun j => S.getD j fallback
    let root := (addr 0).1
    let y := AllSizeS1Geometry.step B x e
    let old := (x root).long
    let new := (y root).long
    Issue old →
    (e≠RearTrace.predecessor root ∧ Issue new ∧ control new=control old ∧
      ∀ j≤len, project addr y j=.empty) ∨
    (e=RearTrace.predecessor root ∧ initial (ctrlOp.read old).toNat old=none ∧
      snapshot new=((.empty,1),0) ∧ ∀ j≤len, project addr y j=.empty) ∨
    (e=RearTrace.predecessor root ∧ Launch old new ∧
      Good anyTag len (project addr y) (.out 0) ∧
      ∀ j, 0<j → j≤len → project addr y j=.empty) := by
  dsimp only
  intro issue
  let addr := fun j => S.getD j fallback
  let root := (addr 0).1
  let y := AllSizeS1Geometry.step B x e
  by_cases E : e=RearTrace.predecessor root
  · subst e
    rcases issue_chart hp C same distinct issue.1 issue.2 with N|⟨a,A,F,G,ctl⟩
    · refine .inr (.inl ⟨rfl,N.1,N.2,?_⟩)
      exact (BStarClearanceBadIssue.restart hp C same distinct clean issue N.1).1
    · refine .inr (.inr ⟨rfl,⟨issue,a,A,?_⟩,G,?_⟩)
      · have K := (root_header hp C same).2
        have read : project addr y 0=atSite (y root).long 0 := by
          change atSite (y root).long (addr 0).2=_
          rw [K]
        exact Prod.ext (Prod.ext (read.symm.trans F) (congrArg (fun q : BitVec 2 × BitVec 9 => q.1) ctl))
          (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) ctl)
      · exact BStarClearanceBadIssue.empty_suffix hp C same clean _ (distinct _)
  · obtain ⟨K,F⟩ := idle_nonown hp C same clean e (distinct e) E
    exact .inl ⟨E,⟨(BStarResetWaitRing.valid_of_control_eq _ _ F).trans issue.1,
      (congrArg (fun q : BitVec 2 × BitVec 9 => q.1.toNat) F).trans issue.2⟩,F,K⟩


open BStarSeparatorRing BStarSeparatorTags BStarSeparatorJoinedTags BStarLongRouting

/-- If an old forward token is parked by a selected link, that link
cannot dirty an old empty destination. Otherwise it writes T at its
source; a surviving F at the source excludes this second branch. -/
theorem link_forward_survivor_empty (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat)
    (hp : 0<p) (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (c : CommandClaim) (d : AtK) (hd : c.destination=some d) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c∈orderedCommands g → d∉discarded g → readK raw d=.empty →
    anyTag.F (readK raw c.source) → anyTag.F (readK out c.source) →
    readK out d=.empty := by
  dsimp only
  intro hc valid E F G
  let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  obtain ⟨oldPayload,P⟩ := F
  have T : anyTag.F (bound g (readK raw) c.source) := by
    unfold bound
    rw [show readK raw c.source=.forward oldPayload from P]
    exact bound_F _ _ _
  obtain ⟨pay,H⟩ := T
  obtain ⟨ne,Link,S⟩ := BStarAcquireReturn.link_shape g c d hc hd
  have noDest : d≠R 0 ∨ g.2.axes.h6=false := by
    by_cases D : d=R 0
    · exact .inr (BStarAcquireJoinedHop.k0_dest g c d hc hd (by rw [D];rfl)).2
    · exact .inl D
  rcases forward_mark g raw c pay hc (by simp [Link]) H with hold|⟨q,move⟩
  · have dsafe : DoorSafe g raw d := by
      rcases noDest with N|N
      · exact safe_nonright _ _ _ N
      · refine ⟨fun _ H => Bool.noConfusion (H.symm.trans N),?_⟩
        intro _ C t Cm hside
        have D := (BStarK0Frame.door_eq g raw C t Cm).1
        have memC : C∈orderedCommands g := by
          rw [←actualOffers_claims g raw]
          exact List.mem_map.mpr ⟨(C,.door t),Cm,rfl⟩
        have dh := (BStarResetChartIndex.selected_door g C memC (D ▸ rfl)).2.1
        exact Bool.noConfusion (dh.symm.trans N)
    have M := hold_avoids g raw c hold d (by simp [Claim.slots,hd])
    exact joined_idle k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x d (.inl (.inl E)) valid M dsafe |>.trans E
  · obtain ⟨A,_⟩ := BStarClearanceForward.move_lands g raw c q d hd move (Ne.symm ne)
    obtain ⟨q',B'⟩ := G
    have Eq := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x c.source
      (fun h z => (S h z).elim)
    have Eq' : readK (patchPair (longWork g raw) raw) c.source=.trail := by
      change decode (readRaw _ c.source)=_
      rw [A,decode_encode]
    exact Token.noConfusion ((Eq.trans Eq').symm.trans B')


theorem outward_suffix {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (op k l : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (kl : l=k ∨ l=k+1) :
    let adr := fun j => S.getD j fall
    let u := project adr x
    let v := project adr (AllSizeS1Geometry.step B x e)
    Good anyTag len u (.out k) → Good anyTag len v (.out l) →
    (∀ j, k<j → j≤len → u j=.empty) →
    ∀ j, l<j → j≤len → v j=.empty := by
  dsimp only
  intro G H E j leJ jl
  let adr := fun j => S.getD j fall
  let u := project adr x
  let y := AllSizeS1Geometry.step B x e
  let v := project adr y
  let M := mark_at hp C e he op W (.out k) (by intro E; cases E) G
  have bound : k≤l := by omega
  by_cases O : M.link j
  · exact (M.ee j O (E j (by omega) jl)
      (E _ (by omega) (M.bound j O))).1
  · by_cases I : ∃ i, i+1=j ∧ M.link i
    · obtain ⟨i,J,L⟩ := I
      by_cases F : i=k
      · subst i
        have eq : l=k := by omega
        have vi : anyTag.F (v k) := eq ▸ H.2.1
        change linkAt hp x e adr len k at L
        obtain ⟨_,cl,d,hc,hd,src,dst⟩ := L
        have old (s : Nat) (a : AtK) (X : adr s=address e a) :
            readK ((x e).long,(x (rightNeighbor e)).long) a=u s :=
          (old_read x e a).trans ((congrArg (atCursor x) X).symm)
        have new (s : Nat) (a : AtK) (X : adr s=address e a) :
            readK (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=v s :=
          (new_read B x e he a).trans ((congrArg (atCursor y) X).symm)
        have out := link_forward_survivor_empty k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
          (x e,x (rightNeighbor e)) cl d hd hc
          (not_discarded hp C W.1 e (k+1) (by omega) d dst)
          ((old _ _ dst).trans (E _ (by omega) (by omega)))
          ((old _ _ src).symm ▸ G.2.1) ((new _ _ src).symm ▸ vi)
        exact (new _ _ dst).symm.trans out ▸ (J ▸ rfl : v j=v (k+1))
      · have R := (M.ee i L (E i (by omega) (by omega))
          (E (i+1) (by omega) (by omega))).2
        rwa [J] at R
    · by_cases T : j=len ∧ M.terminal
      · obtain ⟨rfl,A⟩ := T
        exact M.termE A (E _ (by omega) (Nat.le_refl _))
      · exact (M.idle j jl O (fun i X L => I ⟨i,X,L⟩)
          (fun eq P => T ⟨eq,P⟩)).2.1 (E _ (by omega) jl)


/-- In the clean outward state established by issue and preserved
by every literal outward step, the unique F is the pointed slot. -/
theorem pointed_unique_forward (u : BStarSeparatingRail.Rail) (len k : Nat)
    (G : Good anyTag len u (.out k))
    (clean : ∀ j, k<j → j≤len → u j=.empty) :
    ∀ j≤len, anyTag.F (u j) ↔ j=k := by
  intro j h
  constructor
  · intro F
    by_cases L : j<k
    · rw [G.2.2 j L] at F
      exact (BStarSeparatorParked.forward_not_trail F).elim
    · by_cases R : k<j
      · rw [clean j R h] at F
        exact (BStarSeparatorParked.forward_not_empty F).elim
      · omega
  · rintro rfl
    exact G.2.1

/-- Once on the way back, there are no outward tokens at all, even
before consuming the pointed reply at the source. -/
theorem pointed_backward_no_forward (u : BStarSeparatingRail.Rail) (len k : Nat)
    (G : Good anyTag len u (.back k)) :
    ∀ j≤len, ¬ anyTag.F (u j) := by
  intro j h F
  by_cases L : j<k
  · rw [G.2.2.1 j L] at F
    exact BStarSeparatorParked.forward_not_trail F
  · by_cases R : k<j
    · rw [G.2.2.2 j R h] at F
      exact BStarSeparatorParked.forward_not_empty F
    · have E : j=k := by omega
      subst j
      exact BStarSeparatorParked.disjoint_class _ G.2.1 F

#print axioms idle_launch_or_hold
#print axioms outward_suffix
#print axioms pointed_unique_forward
end L4.BStarOwnerControlHistory
