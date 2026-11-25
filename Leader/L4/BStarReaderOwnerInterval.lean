import Leader.L4.BStarWriterOwnerInterval

namespace L4.BStarReaderOwnerInterval
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport
open BStarH6WordChart BStarLongEvents BStarGrantBirth BStarLongLayout
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongCommand
open BStarAcquireForwardTrace BStarLongGrant BStarGrantWriterHistory
open BStarLongFixedRouting BStarReleaseOrigin BStarPublicationBirth
open BStarLongDoor BStarClearanceSource
open BStarLongGrantProjection

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem no_release_request {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (s : Side) (port : Fin 3) (loc : i=site e s)
    (own : commandOwner (oldH6 B base) i ⟨port.val,by omega⟩=o.val)
    (off : ∀ a, m≠.busy releaseOp a) :
    let y := run x w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    requested (BStarLongCommandData.round g raw).offered s port releaseOp=false := by
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro req
  let y := run x w
  obtain ⟨claim,_,q,_,hs,hj,_,_,Q,F,O⟩ := pre_grant_release_origin _ _ s port req
  let k : Fin 11 := ⟨port.val,by omega⟩
  have addr : address e claim.source=(i,k) :=
    Prod.ext ((congrArg (site e) hs).trans loc.symm) (Fin.ext hj)
  have acts : active (longGeometry B (base i)) k=true := by
    have H := port.isLt
    have A : port.val≠8 := by omega
    have D : port.val≠9 := by omega
    simp [active,k,A,D]
  obtain ⟨j,hj,J⟩ := List.getElem_of_mem (chart.cover (i,k) acts own)
  have idx : S.getD j fall=(i,k) := (List.getElem_eq_getD _).symm.trans J
  have l := chart.length
  have le : j≤len := by omega
  have raw : readK ((y e).long,(y (rightNeighbor e)).long) claim.source=atCursor y (i,k) := by
    rw [BStarResetRailRing.old_read]
    exact congrArg (atCursor y) addr
  have project_q : project (fun a => S.getD a fall) y j=.forward q :=
    (congrArg (atCursor y) idx).trans (raw.symm.trans Q)
  exact off _ (BStarOwnerLaunchOrigin.healthy_forward_origin hp chart sep P now j le q
    project_q releaseOp F O).1

theorem keeps_incidence (x : X) (e i : Fin n) (port : Fin 3) (sep : e≠rightNeighbor e)
    (head : (longGeometry B (x i)).axes.h6=true)
    (coh : conflict (BStarGrantReaderHistory.ports x i)=false)
    (live : canonical (BStarGrantReaderHistory.ports x i) port=true)
    (nr : ∀ s : Side, i=site e s →
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      requested (BStarLongCommandData.round g raw).offered s port releaseOp=false) :
    bit (step x e) i port≠0 ∧ conflict (BStarGrantReaderHistory.ports (step x e) i)=false := by
  have touch (s : Side) (loc : i=site e s) :
      bit (step x e) i port≠0 ∧ conflict (BStarGrantReaderHistory.ports (step x e) i)=false := by
    subst i
    have H := BStarLongGrantProjection.joined_keeps_incidence k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) s port (by cases s <;> exact head) (by cases s <;> exact live) (nr s rfl)
    refine ⟨?_,BStarGrantReaderHistory.mark_coherent hp x e sep s⟩
    cases s
    · simpa [bit,site,AllSizeS1Geometry.step,BStarLongGrantProjection.read,BStarLongGrant.atOld,lane,Pair.map] using
        (show BStarLongGrantProjection.read
          (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .left port≠0 by rw [H]; decide)
    · simpa [bit,site,AllSizeS1Geometry.step,Ne.symm sep,BStarLongGrantProjection.read,BStarLongGrant.atOld,lane,Pair.map] using
        (show BStarLongGrantProjection.read
          (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) .right port≠0 by rw [H]; decide)
  by_cases L : i=e
  · exact touch .left L
  · by_cases R : i=rightNeighbor e
    · exact touch .right R
    · have E : step x e i=x i := by simp [AllSizeS1Geometry.step,L,R]
      constructor
      · unfold bit
        rw [E]
        intro z
        have W : BStarGrantReaderHistory.ports x i port=false := by
          change ((grant port).read (x i).long).getLsbD 0=false
          rw [z]
          rfl
        rw [canonical_clean _ coh port,W] at live
        contradiction
      · unfold BStarGrantReaderHistory.ports; rwa [E]



theorem canonical_live (x : X) (i : Fin n) (port : Fin 3)
    (coh : conflict (BStarGrantReaderHistory.ports x i)=false)
    (H : canonical (BStarGrantReaderHistory.ports x i) port=true) :
    bit x i port≠0 := by
  rw [canonical_clean _ coh] at H
  intro z
  change ((grant port).read (x i).long).getLsbD 0=true at H
  change (grant port).read (x i).long=0 at z
  rw [z] at H
  contradiction
theorem won_live (x : X) (e i : Fin n) (port : Fin 3) (sep : e≠rightNeighbor e)
    (won : WonAt hp x e i port) : bit (step x e) i port≠0 := by
  obtain ⟨s,E,H,win,_⟩ := won
  subst i
  apply canonical_live _ _ _ (BStarGrantReaderHistory.mark_coherent hp x e sep s)
  have K := BStarReaderGrantOrbit.acquisition_seeds k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) s port H win
  cases s
  · simpa [site,AllSizeS1Geometry.step,BStarGrantReaderHistory.ports,BStarLongGrant.atOld,lane,Pair.map] using K
  · simpa [site,AllSizeS1Geometry.step,Ne.symm sep,BStarGrantReaderHistory.ports,BStarLongGrant.atOld,lane,Pair.map] using K


/-- A won reader stays continuously live until its owning controller can
issue a release. No COMMIT exclusion is required. -/
theorem owned_interval {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead : List (Fin n)) (birth i : Fin n) (port : Fin 3) (ne : port≠1) (w : List (Fin n))
    (own : commandOwner (oldH6 B base) i ⟨port.val,by omega⟩=o.val)
    (won : WonAt hp (run x lead) birth i port)
    (atPrefix : ∀ u e v, w=u++e::v →
      let tape := lead++birth::u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle tape m ∧
        Current hp base (fun j => S.getD j fall) len (run x tape) m ∧
        (ctrlOp.read ((run x tape) (S.getD 0 fall).1).long).toNat≠releaseOp ∧
        (longGeometry B ((run x tape) i)).axes.h6=true) :
    let z := run x lead
    let y := step z birth
    Continuous hp y i port w ∧
    ∀ u v, w=u++v →
      let init := (z i).long
      let fin := ((run y u) i).long
      BStarLongPublication.readSel fin=BStarLongPublication.readSel init ∧
      BStarCaptureInterval.payloadView (BStarLongPublication.readSel init) fin=
        BStarCaptureInterval.payloadView (BStarLongPublication.readSel init) init ∧
      canonical (BStarGrantReaderHistory.ports (run y u) i) port=true := by
  dsimp only
  let z := run x lead
  let y := step z birth
  have reindex (u : List (Fin n)) : run x (lead++birth::u)=run y u :=
    BStarResetSchedule.run_append step x lead (birth::u)
  have K (u e v) (E : w=u++e::v)
      (L : bit (run y u) i port≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y u) i)=false) :
      bit (step (run y u) e) i port≠0 ∧
        conflict (BStarGrantReaderHistory.ports (step (run y u) e) i)=false := by
    obtain ⟨m,G,now,pc,header⟩ := atPrefix u e v E
    apply keeps_incidence hp _ e i port (sep e) (reindex u ▸ header) L.2
      (BStarGrantReaderHistory.canonical_of_live _ i port L.2 L.1)
    intro s loc
    exact reindex u ▸ no_release_request hp chart sep G now e i s port loc own (BStarWriterOwnerInterval.not_busy_of_old_pc hp now _ pc)
  have L' (rev : List (Fin n)) (v : List (Fin n)) (E : w=rev.reverse++v) :
      bit (run y rev.reverse) i port≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y rev.reverse) i)=false := by
    induction rev generalizing v with
    | nil => exact ⟨won_live hp z birth i port (sep birth) won,(BStarGrantReaderHistory.birth_step hp z birth i (sep birth) port ne 0 won).2⟩
    | cons e rev ih =>
      have A : w=rev.reverse++e::v := by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using E
      have H := K rev.reverse e v A (ih (e::v) A)
      simpa only [List.reverse_cons,BStarResetSchedule.run_append,BStarResetSchedule.run] using H
  have L (u v : List (Fin n)) (E : w=u++v) :
      bit (run y u) i port≠0 ∧
        conflict (BStarGrantReaderHistory.ports (run y u) i)=false := by
    simpa only [List.reverse_reverse] using
      (L' u.reverse v (by simpa only [List.reverse_reverse] using E))
  have C : Continuous hp y i port w := fun u v E => (L u v E).1
  exact ⟨C,BStarGrantReaderHistory.header_interval hp sep z birth i port ne won w C⟩

#print axioms no_release_request
#print axioms keeps_incidence
#print axioms won_live
#print axioms owned_interval
end L4.BStarReaderOwnerInterval
