import Leader.L4.BStarClearanceForwardService
import Leader.L4.DirtyLeastForward

/-! Exact old provenance of an overlapping field-preparation reservation.
This does not rule out either ordinary data traffic or retaining swaps. -/
namespace L4.DirtyFencePrep
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongWork BStarLongRouting BStarLongEvents
open BStarLongCommandData BStarClearanceCommandFrame BStarClearancePrepOwner
open BStarLongFiberOwner BStarLongFenceTopology BStarClearanceDataChart

theorem prep_cut (g : LongGeometry) (j : Fin 11) (op : Prep) (s : Sheet)
    (h : s∈prepSites g j op) : j.val≤5 ∧ cmdDispl j=dataDispl s := by
  have V : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 ∨
    j.val=6 ∨ j.val=7 ∨ j.val=8 ∨ j.val=9 ∨ j.val=10 := by omega
  rcases V with V|V|V|V|V|V|V|V|V|V|V
  · have E : j=(0 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(1 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(2 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(3 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(4 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(5 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(6 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(7 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(8 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(9 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide
  · have E : j=(10 : Fin 11) := Fin.ext V
    subst j
    cases s <;> cases op <;> cases I : g.inside <;>
      simp [prepSites,I] at h <;> decide

theorem local_reservation_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : At Sheet)
    (h : s∈BStarLongPrep.reserved (round g raw).prep) :
    ∃ C u op, C∈orderedCommands g ∧
      bound g (readK raw) C.source=.forward u ∧
      s.side=C.source.side ∧
      s.occurrence∈prepSites (geometry g C.source.side) C.source.occurrence op ∧
      C.source.occurrence.val≤5 ∧ cmdDispl C.source.occurrence=dataDispl s.occurrence := by
  obtain ⟨C,p,op,G,_,_,side,site⟩ := reserved_from_old_advance g raw s h
  obtain ⟨q,Q⟩ := gated_still_departs g raw C p G
  obtain ⟨u,U⟩ := advance_origin g raw C q Q
  have H : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,Q,rfl⟩
  exact ⟨C,u,op,H,U,side,site,prep_cut _ _ _ _ site⟩

open BStarAcquireVisitOrder BStarResetChartTouch BStarH6WordChart
open BStarAcquireRailCoverage BStarResetMarkAdapter BStarResetChartIndex
open BStarLongFixedRouting BStarAcquireLiteralChain BStarAcquireAnchors

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- A reservation at an owner lane has an old interpreted F in that
owner's chart, at an actual prep-capable address of this same sheet. -/
theorem chart_reservation_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n) (a : At Sheet)
    (ownerLane : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val)
    (h : a∈BStarLongPrep.reserved (round (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long)).prep) :
    ∃ u∈S, u.1=site e a.side ∧ u.2.val≤5 ∧
      (∃ op,a.occurrence∈prepSites (longGeometry B (x u.1)) u.2 op) ∧
      ∃ pay, bind (longGeometry B (x u.1)) u.2 (atSite (x u.1).long u.2)=.forward pay := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨C,pay,op,H,F,E,prep,K,D⟩ := local_reservation_origin g raw a h
  let u := address e C.source
  have eq : u.1=site e a.side := by change site e C.source.side=_; rw [E]
  have own : commandOwner (oldH6 B base) u.1 u.2=o.val := by
    change owner _ _ (cmdDispl C.source.occurrence)=_
    rw [D,eq]
    exact ownerLane
  have hc : C∈orderedCommands (oldPair B base e) :=
    (command_eq B base x same e).symm ▸ H
  have act : active (longGeometry B (base u.1)) u.2=true := by
    cases hd : C.destination with
    | some t =>
        have A := (BStarAcquireChainEndpoints.link_endpoints _ C t hc hd).1
        cases sc : C.source.side <;>
          simpa [geometry,oldPair,u,address,site,sc] using A
    | none =>
        have E : C.source.occurrence.val=0 ∨ C.source.occurrence.val=10 := by
          by_cases A : C.kind=.door
          · exact .inl (congrArg (fun t : AtK => t.occurrence.val) (selected_door _ C hc A).1)
          · exact .inr (BStarAcquireChainEndpoints.terminal _ C hc hd A).2.2.2
        change active (longGeometry B (base u.1)) C.source.occurrence=true
        rcases E with V|V <;> simp [active,V]
  refine ⟨u,chart.cover u act own,eq,K,⟨op,?_⟩,⟨pay,?_⟩⟩
  · cases sc : C.source.side <;> simpa [geometry,g,oldPair,u,address,site,sc] using prep
  · unfold bound at F
    cases sc : C.source.side <;>
      simpa [geometry,g,oldPair,raw,u,address,site,sc,readK,readRaw,lane] using F

/-- Once all chart positions capable of preparing this exact sheet
are forward-free, it receives no same-owner prep reservation, on any
mark for which layout and ownership are as stated. -/
theorem sheet_no_reservation {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n) (a : At Sheet)
    (ownerLane : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val)
    (clear : ∀ u∈S, (∃ op,a.occurrence∈prepSites (longGeometry B (x u.1)) u.2 op) →
      ∀ pay, bind (longGeometry B (x u.1)) u.2 (atSite (x u.1).long u.2)≠.forward pay) :
    a∉BStarLongPrep.reserved (round (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long)).prep := by
  intro h
  obtain ⟨u,U,_,_,P,pay,F⟩ := chart_reservation_origin hp chart same e a ownerLane h
  exact clear u U P pay F

open DirtyLeastForward BStarClearanceIndexedSum BStarClearanceIndexedWait

/-- On an actual pre-service tape where every target-sheet prep
slot precedes the cutoff, no mark in the tape reserves that sheet
for this owner. The tape stays on the very same fixed chart. -/
theorem no_reservation_along {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tape : List (Fin n)) (cutoff : Nat) (sheet : Sheet)
    (onPrep : ∀ u∈S, (∃ op,sheet∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u)
    (good : ∀ pre e post, tape=pre++e::post →
      let z := pre.foldl (AllSizeS1Geometry.step B) x
      (∀ i,Layout B base i=Layout B z i) ∧
      BeforeOwnService hp z (endpoint (oldH6 B base) hh o 0).1 e) :
    ∀ pre e post, tape=pre++e::post → ∀ a : At Sheet, a.occurrence=sheet →
      dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val →
      let z := pre.foldl (AllSizeS1Geometry.step B) x
      a∉BStarLongPrep.reserved (round (oldPair B z e) ((z e).long,(z (rightNeighbor e)).long)).prep := by
  intro pre e post Tape a A Own
  let z := pre.foldl (AllSizeS1Geometry.step B) x
  have same := (good pre e post Tape).1
  have H := ring_frontier_run hp chart sep pre cutoff
    (fun u k v split => good u k (v++e::post) (by rw [Tape,split]; simp [List.append_assoc])) clear
  dsimp only
  intro Live
  obtain ⟨u,U,_,_,⟨op,P⟩,pay,F⟩ := chart_reservation_origin hp chart same e a Own Live
  have sameI : (longGeometry B (base u.1)).inside=(longGeometry B (z u.1)).inside :=
    congrArg (fun b : Bool × Bool × Bool => b.2.1) (same u.1)
  have oldP : sheet∈prepSites (longGeometry B (base u.1)) u.2 op := by
    rw [←A]
    cases op <;> simpa only [prepSites,sameI] using P
  apply H u U (onPrep u U ⟨op,oldP⟩)
  have IF : IsForward (longGeometry B (z u.1),longGeometry B (z u.1)) (L u.2)
      (encode (atSite (z u.1).long u.2)) := ⟨pay,by simpa [BStarLongToken.decode_encode,geometry,L] using F⟩
  have E := (isForward_iff _ _ _).mp IF
  simpa only [ringF,BStarLongToken.decode_encode] using E

end L4.DirtyFencePrep
