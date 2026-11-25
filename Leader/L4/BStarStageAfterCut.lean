import Leader.L4.BStarStageWriterAuth
import Leader.L4.BStarRecoveredHistory

namespace L4.BStarStageAfterCut
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarResetSchedule BStarGeneratedOwner BStarLongEvents BStarGeneratedBandScan
open BStarOwnerRecoveryPass BStarAcquireRailCoverage BStarBodyStageProvenance

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem lower_keeps (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (x : X) (w : List (Fin n)) (I : Q x) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih _ (closed x e I)

/-- On any prefix after the responsible owner's completed recovery,
the literal effective body STAGE is authentic and can only write the
complementary banks of the driver's actual center-header writer.
This is an all-mark property. It does not suppose that the stored
grant itself identifies the command or bank. -/
theorem body_authority_after_credit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {w : List (Fin n)} {a b : Nat}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (credit : BStarRecoveryPass.Credit step (Recovered hp base hh) o x w a b)
    (e i center : Fin n)
    (hdr : oldH6 B base center=true)
    (own : commandOwner (oldH6 B base) center 1=o.val) :
    BodyAuthority hp (run x w) e i center := by
  obtain ⟨lead,reset,tail,W,_,_,rec⟩ := credit
  have initial : Q (run x lead) := lower_keeps hp Q closed x lead I
  obtain ⟨S,len,fall,chart,pc3,_,m,G,_,current⟩ :=
    BStarRecoveredHistory.recovered_suffix hp rec sep Q initial fiber closed tail
  let z := run (run x lead) reset
  have Qz : Q z := lower_keeps hp Q closed _ reset initial
  have replay : run z tail=run x w := by rw [W,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  have now : Current hp base (fun j => S.getD j fall) len (run z tail) m := by
    simpa only [BStarResetSchedule.run_append] using current
  have C : BodyAuthority hp (run z tail) e i center := by
    unfold BodyAuthority
    dsimp only
    intro cl q selected source nearCenter owns inside healthy d decoder
    let y := run z tail
    let adr := address e
    have h6eq : oldH6 B y=oldH6 B base := funext (fun j =>
      (congrArg Prod.fst (fiber y (lower_keeps hp Q closed z tail Qz) j)).symm)
    have cf : physicalOwner (oldH6 B base) e cmdDispl cl.source=o.val := by
      change physicalOwner (oldH6 B y) e cmdDispl cl.source=
        commandOwner (oldH6 B y) center 1 at owns
      rw [h6eq] at owns
      exact owns.trans own
    have eligible : active (longGeometry B (base (adr cl.source).1)) (adr cl.source).2=true := by
      change active (longGeometry B (base (adr cl.source).1)) cl.source.occurrence=true
      unfold active
      simp [nearCenter]
    have mem : adr cl.source∈S := chart.cover _ eligible cf
    obtain ⟨j,hj,K⟩ := List.getElem_of_mem mem
    have lenS := chart.length
    have idx : S.getD j fall=adr cl.source := (List.getElem_eq_getD _).symm.trans K
    have lower : pc z (S.getD 0 fall).1<6 := by
      change pc z (S.getD 0 fall).1=3 at pc3
      omega
    apply BStarStageWriterAuth.stage_writer hp chart Q Qz fiber closed sep G now lower j
      (by omega) e cl q idx center hdr own d
    · exact selected
    · exact healthy
    · exact decoder
  rwa [replay] at C

open BStarClearanceOffset

/-- After the first completed recovery pass, every possible later
old mark has the effective STAGE writer/selector law at its center
word. The second pass may still be used to retire pre-A acquisitions.
This theorem does not give a bound in random interaction time. -/
theorem all_body_after_first_cut {base x : X} (hh : ∃ i,oldH6 B base i=true)
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
      ∀ tail e i center, oldH6 B base center=true →
        BodyAuthority hp (run x (u++tail)) e i center := by
  obtain ⟨u,v,U,V,A,_⟩ := two_recoveries hp hh charts sep head cont Q closed fiber heads conts cb owners I cx
  refine ⟨u,v,U.1,V.1,?_⟩
  intro tail e i center hdr
  obtain ⟨o,M,own⟩ := cover center
  obtain ⟨a,b,_,B0,C⟩ := A o M
  have atA := BStarRecoveryPass.credit_prefix step C B0
  exact body_authority_after_credit hp sep Q I fiber closed
    (BStarRecoveryPass.credit_append step atA tail) e i center hdr own

end L4.BStarStageAfterCut
