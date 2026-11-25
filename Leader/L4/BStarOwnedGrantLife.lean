import Leader.L4.BStarCommitOperands

namespace L4.BStarOwnedGrantLife
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
open BStarReaderOwnerInterval

/-- A won grant stays continuously live until its owning controller can
issue a release. No COMMIT exclusion is required. -/
theorem continuous {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead : List (Fin n)) (birth i : Fin n) (port : Fin 3) (w : List (Fin n))
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
    Continuous hp y i port w := by
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
    | nil =>
      refine ⟨won_live hp z birth i port (sep birth) won,?_⟩
      obtain ⟨s,E,_⟩ := won
      subst i
      exact BStarGrantReaderHistory.mark_coherent hp z birth (sep birth) s
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
  exact fun u v E => (L u v E).1

def writer_acquisition {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (cut tape lead : List (Fin n)) (birth i : Fin n)
    (post : List (Fin n)) (E : tape=lead++birth::post) (after : cut.length≤lead.length)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (won : WonAt hp (run x lead) birth i 1)
    (atPrefix : ∀ u e v, post=u++e::v →
      let w := lead++birth::u
      ∃ m, GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m ∧
        Current hp base (fun j => S.getD j fall) len (run x w) m ∧
        (ctrlOp.read ((run x w) (S.getD 0 fall).1).long).toNat≠releaseOp ∧
        (longGeometry B ((run x w) i)).axes.h6=true)
    (before : BStarGrantWriterHistory.BeforePublication hp (step (run x lead) birth) i post) :
    BStarCommitOperands.Acquisition hp x cut tape i 1 :=
  BStarCommitOperands.Acquisition.writer hp x cut tape i lead birth post E after won
    (continuous hp chart sep lead birth i 1 post own won atPrefix) before

#print axioms continuous
#print axioms writer_acquisition
end L4.BStarOwnedGrantLife
