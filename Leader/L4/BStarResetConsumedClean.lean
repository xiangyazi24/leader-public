import Leader.L4.BStarResetChartService
import Leader.L4.BStarResetQuietAdapter
import Leader.L4.BStarSeparatorControl

namespace L4.BStarResetConsumedClean
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

/-- The whole suffix stays empty across the separate old-root door mark.
The proof inspects the old pair only: root D cannot advance forward on
its outgoing DE link, and suffix incidences are otherwise EE or terminal E. -/
theorem suffix_empty_any {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : Clean (project (fun j => S.getD j fallback)) BStarSeparatorControl.anyTag len x)
    (e : Fin n) (he : e≠rightNeighbor e) :
    ∀ j, 0<j → j≤len →
      project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e) j=.empty := by
  intro j hj hlen
  let addr := fun j => S.getD j fallback
  let U := project addr x
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have read (j : Nat) (a : AtK) (H : addr j=address e a) : readK raw a=U j :=
    (old_read x e a).trans ((congrArg (atCursor x) H).symm)
  have Eread (j : Nat) (a : AtK) (H : addr j=address e a) (hj : 0<j) (hl : j≤len) :
      bound g (readK raw) a=.empty := by
    have E := (read j a H).trans (clean.2 j hj hl)
    exact (quiet_bound g (readK raw) a (.inl E)).trans E
  have links (i : Nat) (Lh : linkAt hp x e addr len i) :
      ∃ (a b : AtK), addr i=address e a ∧ addr (i+1)=address e b ∧
        avoids a (middle g raw) ∧ avoids b (middle g raw) := by
    obtain ⟨hi,K,d,hK,hd,hs,ht⟩ := Lh
    have ht' := Eread (i+1) d ht (by omega) (by omega)
    have H : LinkHold (bound g (readK raw) K.source) (bound g (readK raw) d) := by
      by_cases Zi : i=0
      · subst i
        obtain ⟨q,D⟩ := clean.1
        have Rp : readK raw K.source=.reply q := (read 0 K.source hs).trans D
        unfold bound
        rw [Rp]
        obtain ⟨v,V⟩ := BStarSeparatorControl.bound_D (geometry g K.source.side) K.source.occurrence q
        rw [V]
        change LinkHold (.reply v) (bound g (readK raw) d)
        rw [ht']
        exact .de v
      · rw [Eread i K.source hs (by omega) (by omega),ht']
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
      omega
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
        rcases K with ⟨Z,_,_⟩|⟨J,T⟩|L|⟨i,I,L⟩
        · omega
        · subst j
          obtain ⟨K,M,hk,_,_,S⟩ := T
          have A := address_inj e he a K.source (H.symm.trans S)
          subst a
          exact terminal_avoids g raw K M hk (by rw [Eread len K.source H hj hlen]; exact .e)
        · obtain ⟨b,d,HB,_,hb,_⟩ := links j L
          exact (address_inj e he a b (H.symm.trans HB)).symm ▸ hb
        · obtain ⟨b,d,_,D,_,hd⟩ := links i L
          have eq : addr j=address e d := I ▸ D
          exact (address_inj e he a d (H.symm.trans eq)).symm ▸ hd
      intro w hw
      exact G w (List.mem_flatMap.mpr ⟨v,hv,hw⟩)
    have R := idle_at hp x e he a (.inl (.inl ((read j a H).trans (clean.2 j hj hlen)))) hn hm safe
    exact (congrArg (atCursor (AllSizeS1Geometry.step B x e)) H).trans
      (R.trans ((congrArg (atCursor x) H).symm.trans (clean.2 j hj hlen)))
  by_cases hl : (addr j).1=e
  · exact selected (L (addr j).2) (Prod.ext hl rfl)
  · by_cases hr : (addr j).1=rightNeighbor e
    · exact selected (R (addr j).2) (Prod.ext hr rfl)
    · exact (idle_off_pair hp x e (addr j) hl hr).trans (clean.2 j hj hlen)


theorem suffix_empty {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (op : Nat) (ho : op<3)
    (clean : Clean (project (fun j => S.getD j fallback)) (resetTag op) len x)
    (e : Fin n) (he : e≠rightNeighbor e) :
    ∀ j, 0<j → j≤len →
      project (fun j => S.getD j fallback) (AllSizeS1Geometry.step B x e) j=.empty := by
  apply suffix_empty_any hp C same _ e he
  obtain ⟨q,H,F⟩ := clean.1
  refine ⟨?_,clean.2⟩
  obtain ⟨v,V⟩ := (BStarResetTaggedRows.bind_finish (longGeometry B (x (S.getD 0 fallback).1)) 0 q
    (reset_of_holds op ho q H)).2
  exact ⟨v,F.trans V⟩


theorem consumed_clean {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (op : Nat) (ho : op<3)
    (wait : Waiting hp base (S.getD 0 fallback).1 op x)
    (clean : Clean (project (fun j => S.getD j fallback)) (resetTag op) len x)
    (distinct : ∀ e : Fin n, e≠rightNeighbor e) :
    let root := (S.getD 0 fallback).1
    let door := RearTrace.predecessor root
    let y := AllSizeS1Geometry.step B x door
    (∀ j≤len, project (fun j => S.getD j fallback) y j=.empty) ∧
    (ctrlPhase.read (y root).long)=1 ∧
    (project (fun j => S.getD j fallback) x 0=finish (BStarResetTaggedRows.resetPayload op) →
      (ctrlOp.read (y root).long)=BitVec.ofNat 9 (op+1)) := by
  dsimp only
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let y := AllSizeS1Geometry.step B x door
  let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C wait.1
  have T {z : XX} : track z 0=atCursor z (root,0) :=
    congrArg (atCursor z) (Prod.ext rfl K)
  have q := source_service hp x door (distinct door) op ho (by rw [R]; exact H)
    (by rw [R]; exact wait.2.1)
    (by rw [R]; exact wait.2.2.1)
    (by rw [R]; exact wait.2.2.2)
    (by rw [R,←T]; exact clean.1)
  dsimp only at q
  rw [R] at q
  refine ⟨?_,q.2.1,fun h => q.2.2 (T.symm.trans h)⟩
  intro j hj
  by_cases Z : j=0
  · subst j
    exact T.trans q.1
  · exact suffix_empty hp C wait.1 op ho clean door (distinct door) j (by omega) hj

#print axioms suffix_empty_any
#print axioms suffix_empty
#print axioms consumed_clean
end L4.BStarResetConsumedClean
