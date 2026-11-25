import Leader.L4.BStarPublicationBirth
import Leader.L4.BStarReleaseOrigin

namespace L4.BStarWriterOwnerInterval
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport
open BStarH6WordChart BStarLongEvents BStarGrantBirth BStarLongLayout
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongCommand
open BStarAcquireForwardTrace BStarLongGrant BStarGrantWriterHistory
open BStarLongFixedRouting BStarReleaseOrigin BStarPublicationBirth
open BStarLongDoor BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem no_publication {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (off : ∀ a, m≠.busy commitOp a) :
    NoPublication hp (run x w) e i := by
  classical
  apply Classical.byContradiction
  intro pub
  obtain ⟨j,_,_,E,_⟩ := commit_from_owner hp chart sep P now e i own pub
  exact off _ E

theorem no_release_request {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (s : Side) (loc : i=site e s)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (off : ∀ a, m≠.busy releaseOp a) :
    let y := run x w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    requested (BStarLongCommandData.round g raw).offered s 1 releaseOp=false := by
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro req
  let y := run x w
  obtain ⟨claim,_,q,_,hs,hj,_,_,Q,F,O⟩ := pre_grant_release_origin _ _ s 1 req
  have addr : address e claim.source=(i,1) :=
    Prod.ext ((congrArg (site e) hs).trans loc.symm) (Fin.ext hj)
  have acts : active (longGeometry B (base i)) (1 : Fin 11)=true := rfl
  obtain ⟨j,hj,J⟩ := List.getElem_of_mem (chart.cover (i,1) acts own)
  have idx : S.getD j fall=(i,1) := (List.getElem_eq_getD _).symm.trans J
  have l := chart.length
  have le : j≤len := by omega
  have raw : readK ((y e).long,(y (rightNeighbor e)).long) claim.source=atCursor y (i,1) := by
    rw [BStarResetRailRing.old_read]
    exact congrArg (atCursor y) addr
  have project_q : project (fun a => S.getD a fall) y j=.forward q :=
    (congrArg (atCursor y) idx).trans (raw.symm.trans Q)
  exact off _ (BStarOwnerLaunchOrigin.healthy_forward_origin hp chart sep P now j le q
    project_q releaseOp F O).1

/-- Literal held writer survives a mark if the old touched header has
no effective own release request. No assumption about COMMIT is used. -/
theorem keeps_writer (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (head : (longGeometry B (x i)).axes.h6=true)
    (coh : conflict (BStarGrantReaderHistory.ports x i)=false)
    (live : canonical (BStarGrantReaderHistory.ports x i) 1=true)
    (nr : ∀ s : Side, i=site e s →
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      requested (BStarLongCommandData.round g raw).offered s 1 releaseOp=false) :
    bit (step x e) i 1≠0 ∧ conflict (BStarGrantReaderHistory.ports (step x e) i)=false := by
  have touch (s : Side) (loc : i=site e s) :
      bit (step x e) i 1≠0 ∧ conflict (BStarGrantReaderHistory.ports (step x e) i)=false := by
    subst i
    have H := BStarLongGrantProjection.joined_keeps_incidence k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) s 1 (by cases s <;> exact head) (by cases s <;> exact live) (nr s rfl)
    refine ⟨?_,BStarGrantReaderHistory.mark_coherent hp x e sep s⟩
    cases s
    · simpa [bit,site,AllSizeS1Geometry.step,BStarLongGrantProjection.read,BStarLongGrant.atOld,lane,Pair.map] using
        (show BStarLongGrantProjection.read
          (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .left 1≠0 by rw [H]; decide)
    · simpa [bit,site,AllSizeS1Geometry.step,Ne.symm sep,BStarLongGrantProjection.read,BStarLongGrant.atOld,lane,Pair.map] using
        (show BStarLongGrantProjection.read
          (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .right 1≠0 by rw [H]; decide)
  by_cases L : i=e
  · exact touch .left L
  · by_cases R : i=rightNeighbor e
    · exact touch .right R
    · have E : step x e i=x i := by simp [AllSizeS1Geometry.step,L,R]
      constructor
      · unfold bit
        rw [E]
        intro z
        have W : BStarGrantReaderHistory.ports x i 1=false := by
          change ((grant 1).read (x i).long).getLsbD 0=false
          rw [z]
          rfl
        simp [canonical,W] at live
      · unfold BStarGrantReaderHistory.ports; rwa [E]


theorem canonical_one_live (y : X) (i : Fin n)
    (H : canonical (BStarGrantReaderHistory.ports y i) 1=true) : bit y i 1≠0 := by
  intro z
  have W : BStarGrantReaderHistory.ports y i 1=false := by
    change ((grant 1).read (y i).long).getLsbD 0=false
    change (grant 1).read (y i).long=0 at z
    rw [z]
    rfl
  simp [canonical,W] at H

theorem won_live (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (won : WonAt hp x e i 1) : bit (step x e) i 1≠0 := by
  obtain ⟨s,E,H,win,_⟩ := won
  subst i
  apply canonical_one_live
  have K := BStarReaderGrantOrbit.acquisition_seeds k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) s 1 H win
  cases s
  · simpa [site,AllSizeS1Geometry.step,BStarGrantReaderHistory.ports,BStarLongGrant.atOld,lane,Pair.map] using K
  · simpa [site,AllSizeS1Geometry.step,Ne.symm sep,BStarGrantReaderHistory.ports,BStarLongGrant.atOld,lane,Pair.map] using K

theorem not_busy_of_old_pc {base y : X} {addr : Nat → Pos n} {len : Nat}
    {m : Mode} (N : Current hp base addr len y m) (op : Nat)
    (pc : (ctrlOp.read (y (addr 0).1).long).toNat≠op) :
    ∀ a, m≠.busy op a := by
  intro a E
  subst m
  exact pc N.1.2.2.2

/-- The owner phase is checked against the literal old state before
each mark, using a generated history beginning at its own reset.
The two op exclusions are independent. -/
theorem owned_interval {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead : List (Fin n)) (birth i : Fin n) (w : List (Fin n))
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (won : WonAt hp (run x lead) birth i 1)
    (atPrefix : ∀ u e v, w=u++e::v →
      let tape := lead++birth::u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle tape m ∧
        Current hp base (fun j => S.getD j fall) len (run x tape) m ∧
        (ctrlOp.read ((run x tape) (S.getD 0 fall).1).long).toNat≠releaseOp ∧
        (ctrlOp.read ((run x tape) (S.getD 0 fall).1).long).toNat≠commitOp ∧
        (longGeometry B ((run x tape) i)).axes.h6=true) :
    let z := run x lead
    let y := step z birth
    BeforePublication hp y i w ∧ Continuous hp y i 1 w ∧
    ∀ u v, w=u++v →
      let init := (z i).long
      let fin := ((run y u) i).long
      BStarLongPublication.readSel fin=BStarLongPublication.readSel init ∧
      BStarCaptureInterval.payloadView (BStarLongPublication.readSel init) fin=
        BStarCaptureInterval.payloadView (BStarLongPublication.readSel init) init ∧
      canonical (BStarGrantReaderHistory.ports (run y u) i) 1=true ∧
      BStarGrantReaderHistory.ports (run y u) i 0=false ∧
      BStarGrantReaderHistory.ports (run y u) i 2=false := by
  dsimp only
  let z := run x lead
  let y := step z birth
  have reindex (u : List (Fin n)) : run x (lead++birth::u)=run y u :=
    BStarResetSchedule.run_append step x lead (birth::u)
  have P : BeforePublication hp y i w := by
    intro u e v E
    obtain ⟨m,G,now,_,pc,_⟩ := atPrefix u e v E
    exact reindex u ▸ no_publication hp chart sep G now e i own (not_busy_of_old_pc hp now _ pc)
  have K (u e v) (E : w=u++e::v)
      (L : bit (run y u) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y u) i)=false) :
      bit (step (run y u) e) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (step (run y u) e) i)=false := by
    obtain ⟨m,G,now,pc,_,header⟩ := atPrefix u e v E
    apply keeps_writer hp _ e i (sep e) (reindex u ▸ header) L.2
      (BStarGrantReaderHistory.canonical_of_live _ i 1 L.2 L.1)
    intro s loc
    exact reindex u ▸ no_release_request hp chart sep G now e i s loc own (not_busy_of_old_pc hp now _ pc)
  have L' (rev : List (Fin n)) (v : List (Fin n)) (E : w=rev.reverse++v) :
      bit (run y rev.reverse) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y rev.reverse) i)=false := by
    induction rev generalizing v with
    | nil => exact ⟨won_live hp z birth i (sep birth) won,(birth_step hp z birth i (sep birth) 0 won).2⟩
    | cons e rev ih =>
      have A : w=rev.reverse++e::v := by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using E
      have H := K rev.reverse e v A (ih (e::v) A)
      simpa only [List.reverse_cons,BStarResetSchedule.run_append,BStarResetSchedule.run] using H
  have L (u v : List (Fin n)) (E : w=u++v) :
      bit (run y u) i 1≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y u) i)=false := by
    simpa only [List.reverse_reverse] using
      (L' u.reverse v (by simpa only [List.reverse_reverse] using E))
  have C : Continuous hp y i 1 w := fun u v E => (L u v E).1
  exact ⟨P,C,header_interval hp sep z birth i won w C P⟩

#print axioms no_publication
#print axioms no_release_request
#print axioms keeps_writer
#print axioms owned_interval
end L4.BStarWriterOwnerInterval
