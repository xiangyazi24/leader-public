import Leader.L4.BStarGrantWriterHistory
import Leader.L4.BStarFirstCut
import Leader.L4.BStarWonCapture
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarRecoveredHistory

namespace L4.BStarPublicationBirth
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport
open BStarH6WordChart BStarLongEvents BStarGrantBirth BStarFirstCut
open BStarLongLayout BStarLongPublication

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A physical publication always has its actual live old center
writer, even when the inherited command could not be authenticated. -/
theorem publication_ne_zero (x : X) (e i : Fin n)
    (pub : ¬ BStarGrantWriterHistory.NoPublication hp x e i) :
    bit x i 1≠0 := by
  obtain ⟨_,C,q,b,_,_,_,literal⟩ := BStarGrantWriterHistory.stopping_commit hp x e i pub
  obtain ⟨_,_,_,_,d,_,_,authorized⟩ := literal
  intro zero
  change (grant 1).read (x i).long=0 at zero
  simp [BStarLongPublication.guard,BStarLongPublication.typedGuard,zero] at authorized

/-- The writer authorizing an actual post-second-cut physical commit
has a won ACQUIRE strictly after the first cut. This does not infer
that the COMMIT packet itself was generated from that exact acquisition. -/
theorem committed_writer_after {x : X} {u v : List (Fin n)}
    (H : ∀ tail i j, bit (run x ((u++v)++tail)) i j≠0 →
      BirthAfter hp x ((u++v)++tail) i j (u.length+1))
    (tail : List (Fin n)) (mark i : Fin n)
    (pub : ¬ BStarGrantWriterHistory.NoPublication hp (run x ((u++v)++tail)) mark i) :
    BirthAfter hp x ((u++v)++tail) i 1 (u.length+1) :=
  H tail i 1 (publication_ne_zero hp _ mark i pub)

#print axioms publication_ne_zero
#print axioms committed_writer_after

open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongCommand
open BStarAcquireForwardTrace

/-- After that owner's reset, an authorized physical publication
is genuinely issued COMMIT from its own controller on this same
tape, not an inherited syntactically valid COMMIT packet. This is
command provenance, not yet computation or descriptor ancestry. -/
theorem commit_from_owner {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (P : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (e i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (pub : ¬ BStarGrantWriterHistory.NoPublication hp (run x w) e i) :
    ∃ j≤len, S.getD j fall=(i,1) ∧ m=.busy commitOp (.out j) ∧
      BStarOwnerLaunchOrigin.Found hp base (fun j => S.getD j fall) len
        commitOp x w (.out j) := by
  let y := run x w
  obtain ⟨s,C,p,b,loc,H,selected,literal⟩ :=
    BStarGrantWriterHistory.stopping_commit hp y e i pub
  have U : address e C.source=(i,1) :=
    Prod.ext ((congrArg (site e) H).trans loc.symm) (Fin.ext literal.1)
  have acts : active (longGeometry B (base i)) (1 : Fin 11)=true := by
    unfold active
    rfl
  have J := chart.cover (i,1) acts own
  obtain ⟨j,hj,Z⟩ := List.getElem_of_mem J
  have idx : S.getD j fall=(i,1) := (List.getElem_eq_getD _).symm.trans Z
  have l := chart.length
  have le : j≤len := by omega
  obtain ⟨q,Q,V,O⟩ := BStarForwardProvenance.offer_origin _ _ C p selected literal.2.2.1
  have raw : readK ((y e).long,(y (rightNeighbor e)).long) C.source=
      atCursor y (i,1) := by
    rw [BStarResetRailRing.old_read]
    exact congrArg (atCursor y) U
  have read : project (fun j => S.getD j fall) y j=.forward q :=
    (congrArg (atCursor y) idx).trans (raw.symm.trans Q)
  exact ⟨j,le,idx,BStarOwnerLaunchOrigin.healthy_forward_origin hp chart sep P now j le q read
    commitOp V ((congrArg BitVec.toNat O).trans literal.2.2.2.1)⟩

#print axioms commit_from_owner

open BStarOwnerRecoveryPass BStarLongFixedRouting BStarLongDoor BStarClearanceSource

/-- A historical reset credit on the common physical word suffices:
any later authorized publication at an owned K1 has a freshly
generated, genuinely issued COMMIT after that credit. No claim is
made about publications that precede its owner's recovery. -/
theorem commit_after_credit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {w : List (Fin n)} {a b : Nat}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (credit : BStarRecoveryPass.Credit step (Recovered hp base hh) o x w a b)
    (e i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (pub : ¬ BStarGrantWriterHistory.NoPublication hp (run x w) e i) :
    ∃ pre door post root, w=pre++door::post ∧ b≤pre.length ∧
      let z := run x pre
      door=RearTrace.predecessor root ∧
      Launch (z root).long (step z door root).long ∧
      (ctrlOp.read (z root).long).toNat=commitOp := by
  obtain ⟨lead,reset,tail,W,_,bound,rec⟩ := credit
  have keep (z : X) (w : List (Fin n)) (K : Q z) : Q (run z w) := by
    induction w generalizing z with
    | nil => exact K
    | cons e w ih => exact ih _ (closed z e K)
  have initial : Q (run x lead) := keep _ _ I
  obtain ⟨S,len,fall,chart,_,_,m,G,_,N⟩ :=
    BStarRecoveredHistory.recovered_suffix hp rec sep Q initial fiber closed tail
  let z := run (run x lead) reset
  have F : run z tail=run x w := by
    rw [W,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  have N' : Current hp base (fun j => S.getD j fall) len (run z tail) m := by
    simpa only [BStarResetSchedule.run_append] using N
  obtain ⟨_,_,_,_,⟨pre,post,door,spl,hdr,L,PC,_⟩⟩ :=
    commit_from_owner hp chart sep G N' e i own (F.symm ▸ pub)
  refine ⟨(lead++reset)++pre,door,post,(S.getD 0 fall).1,?_,?_,?_⟩
  · rw [W,spl]
    simp only [List.append_assoc]
  · rw [bound]
    simp only [List.length_append]
    omega
  · simp only [BStarResetSchedule.run_append]
    exact ⟨hdr,L,PC⟩

#print axioms commit_after_credit

open BStarResetNoAcquire BStarClearanceOffset

/-- On two real recovery passes, every post-second-cut publication has
a genuine source COMMIT issue strictly later than the first pass.
This is the unconditional event-authentication layer; the result
does not yet identify the event value with nativeSpec. -/
theorem two_pass_publication_origin {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (charts : ∀ o : Owners (oldH6 B base), ∃ S len fall, Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (fiber : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (owners : List (Owners (oldH6 B base)))
    (cover : ∀ i : Fin n, ∃ o∈owners, commandOwner (oldH6 B base) i 1=o.val)
    (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    ∃ u v, Q (run x u) ∧ Q (run x (u++v)) ∧
      ∀ tail e i, ¬ BStarGrantWriterHistory.NoPublication hp (run x ((u++v)++tail)) e i →
        ∃ pre door post root, ((u++v)++tail)=pre++door::post ∧ u.length<pre.length ∧
          let z := run x pre
          door=RearTrace.predecessor root ∧
            Launch (z root).long (step z door root).long ∧ (ctrlOp.read (z root).long).toNat=commitOp := by
  obtain ⟨u,v,U,V,_,F⟩ := two_recoveries hp hh charts sep head cont Q closed fiber heads conts cb owners I cx
  refine ⟨u,v,U.1,V.1,?_⟩
  intro tail e i pub
  obtain ⟨o,M,own⟩ := cover i
  obtain ⟨a,b,lower,order,credit⟩ := F o M
  obtain ⟨p,door,q,root,W,after,L⟩ :=
    commit_after_credit hp sep Q I fiber closed (BStarRecoveryPass.credit_append step credit tail)
      e i own pub
  exact ⟨p,door,q,root,W,by omega,L⟩

#print axioms two_pass_publication_origin
end L4.BStarPublicationBirth
