import Leader.L4.BStarCommitNoPrior
import Leader.L4.BStarWriterTransferWindow

namespace L4.BStarBeforeCommitWindow
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarLongDoor BStarLongCommand
open BStarGrantWriterHistory BStarWriterTransferWindow BStarGeneratedBandScan BStarSeparatingRail
open BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem before_append (i : Fin n) (x : X) (u v : List (Fin n))
    (H : BeforePublication hp x i u) (K : BeforePublication hp (run x u) i v) :
    BeforePublication hp x i (u++v) := by
  intro pre e tail E
  rcases List.append_eq_append_iff.mp E with ⟨q,P,F⟩|⟨q,P,F⟩
  · rw [P,BStarResetSchedule.run_append]
    exact K q e tail F
  · cases q with
    | nil =>
      simp only [List.append_nil] at P
      rw [←P]
      exact K [] e tail F.symm
    | cons m q =>
      have F' : e::tail=m::(q++v) := F
      have E := (List.cons.inj F').1
      subst m
      exact H pre e q P

theorem before_single (x : X) (i e : Fin n) (H : NoPublication hp x e i) :
    BeforePublication hp x i [e] := by
  intro u d v E
  cases u with
  | nil =>
    obtain ⟨D,_⟩ := List.cons.inj E
    subst d
    exact H
  | cons h u =>
    have L := congrArg List.length E
    simp only [List.length_cons,List.length_append,List.length_nil] at L
    omega

/-- On a post-RESET generated owner, an old-PC exclusion establishes
the actual no-publication fact at a prefix. Idle PC411 itself
does not publish; this also covers its issue mark. -/
theorem no_pub_from_issue_or_pc {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ready : Current hp base (fun j => S.getD j fall) len x .idle)
    (w : List (Fin n)) (i e : Fin n)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (H : Issue (run x w (S.getD 0 fall).1).long ∨ pc (run x w) (S.getD 0 fall).1≠411) :
    NoPublication hp (run x w) e i := by
  obtain ⟨m,P,_,now⟩ := generated_word hp C Q fiber
    (fun z J e => closed z e J) sep w .idle I ready
  apply BStarWriterOwnerInterval.no_publication hp C sep P now e i own
  intro a E
  subst m
  rcases H with H|H
  · exact (show (1:Nat)≠2 by decide) (H.2.symm.trans now.1.2.2.1)
  · exact H now.1.2.2.2

/-- Stitch no-publication facts before COMMIT issue and on its own
in-flight route to the same center K1. Includes the literal own
issue mark, which cannot also publish on the old pair. -/
theorem before_commit_issue_and_flight {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ready : Current hp base (fun j => S.getD j fall) len x .idle)
    (lead middle post : List (Fin n)) (issue i : Fin n) (k : Nat) (hk : k≤len)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (center : S.getD k fall=(i,1))
    (safe : SafePC hp (S.getD 0 fall).1 (run x lead) middle)
    (launch : Launch (run x (lead++middle) (S.getD 0 fall).1).long
      (step (run x (lead++middle)) issue (S.getD 0 fall).1).long)
    (flight : BusyOnly hp base (fun j => S.getD j fall) len commitOp
        (step (run x (lead++middle)) issue) (.out 0) post (.out k)) :
    BeforePublication hp (run x lead) i (middle++issue::post) := by
  have head : BeforePublication hp (run x lead) i middle := by
    intro pre e tail E
    have J := (safe pre e tail E).2
    have W : run x (lead++pre)=run (run x lead) pre := BStarResetSchedule.run_append _ _ _ _
    rw [←W] at J ⊢
    exact no_pub_from_issue_or_pc hp C Q I fiber closed sep ready _ i e own (.inr J)
  refine before_append hp i _ middle (issue::post) head ?_
  rw [←BStarResetSchedule.run_append]
  change BeforePublication hp (run x (lead++middle)) i ([issue]++post)
  refine before_append hp i _ [issue] post ?_ ?_
  · exact before_single hp _ i issue
      (no_pub_from_issue_or_pc hp C Q I fiber closed sep ready _ i issue own (.inl launch.1))
  · exact BStarCommitNoPrior.before_center hp flight sep i k hk center k rfl (Nat.le_refl _)

end L4.BStarBeforeCommitWindow
