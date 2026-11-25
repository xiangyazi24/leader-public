import Leader.L4.BStarResetChartService
import Leader.L4.BStarResetQuietAdapter
import Leader.L4.BStarClearanceSource

namespace L4.BStarClearanceBadIssue
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
theorem empty_suffix {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty)
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

open BStarClearanceSource BStarResetControllerEntry BStarAcquireWaitControl

/-- A valid old ISSUE on an empty rail with no legal operand does not
launch a separator. Its actual incoming source mark leaves the complete
rail empty and installs a new valid ISSUE with opcode zero. -/
theorem restart {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (distinct : ∀ e : Fin n, e≠rightNeighbor e)
    (clean : ∀ j≤len, project (fun j => S.getD j fallback) x j=.empty) :
    let root := (S.getD 0 fallback).1
    let w := (x root).long
    let door := RearTrace.predecessor root
    let y := AllSizeS1Geometry.step B x door
    Issue w → initial (ctrlOp.read w).toNat w=none →
    (∀ j≤len, project (fun j => S.getD j fallback) y j=.empty) ∧
      Issue (y root).long ∧ (ctrlOp.read (y root).long).toNat=0 := by
  dsimp only
  intro I bad
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let y := AllSizeS1Geometry.step B x door
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C same
  have U := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x door,x (rightNeighbor door))
    (by change oldH6 B x (rightNeighbor door)=true; rwa [R])
    (by rw [R]; exact I.1) (by rw [R]; exact I.2)
  have Y : y root=(largePair B (x door,x (rightNeighbor door))).2 := by
    simp only [y,AllSizeS1Geometry.step,←R,if_neg (Ne.symm (distinct door)),if_true]
  have P : snapshot (y root).long=((.empty,1),0) := by
    rw [Y]
    let w := (x (rightNeighbor door)).long
    change snapshot (largePair B (x door,x (rightNeighbor door))).2.long =
      (match initial (ctrlOp.read w).toNat w with
       | none => ((.empty,1),0)
       | some a => ((forward (ctrlOp.read w).toNat a,2),ctrlOp.read w)) at U
    have W : initial (ctrlOp.read w).toNat w=none := by
      unfold w
      rwa [R]
    rw [W] at U
    exact U
  have rootE : atSite (y root).long 0=.empty := congrArg (fun s => s.1.1) P
  have I0 : Issue (y root).long := issue_of_snapshot (by decide : 0<413) P
  have op0 : (ctrlOp.read (y root).long).toNat=0 := congrArg (fun s => s.2.toNat) P
  refine ⟨?_,I0,op0⟩
  intro j hj
  by_cases Z : j=0
  · subst j
    change atSite (y root).long (S.getD 0 fallback).2=.empty
    rwa [K]
  · exact empty_suffix hp (x := x) C same clean door (distinct door) j (by omega) hj

end L4.BStarClearanceBadIssue
