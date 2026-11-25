import Leader.L4.BStarCustodyCuts
import Leader.L4.BStarRecoveredHistory

namespace L4.BStarReceiptRecoveredTour
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireAnchors BStarLongFixedRouting
open BStarResetChartTouch BStarResetMarkAdapter BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarLongCommand BStarCustodyCuts
open BStarLongFiberOwner BStarLongLayout
open BStarAcquireLiteralChain BStarLongDoor BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A generated history at the actual old publication mark. Its
origin is not a favourable new recovery: the mid segment is the
center owner's credited recovery inside the second pass. -/
def CommitTour (base x : X) (u v tail : List (Fin n)) (i : Fin n) : Prop :=
  ∃ (hh : ∃ j,oldH6 B base j=true) (o : Owners (oldH6 B base))
    (pre reset rest : List (Fin n)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
    (k : Nat),
    (u++v)++tail=pre++reset++rest ∧
    Recovered hp base hh o (run x pre) reset ∧
    u.length≤pre.length ∧ 0<reset.length ∧ (pre++reset).length≤(u++v).length ∧
    commandOwner (oldH6 B base) i 1=o.val ∧
    Chart hp base hh o S len fall ∧ k≤len ∧ S.getD k fall=(i,1) ∧
    let addr := fun j => S.getD j fall
    let origin := run x (pre++reset)
    let old := run x ((u++v)++tail)
    (ctrlOp.read (origin (addr 0).1).long).toNat=3 ∧
    Current hp base addr len origin .idle ∧
    GeneratedOwner hp base addr len origin .idle rest (.busy commitOp (.out k)) ∧
    Current hp base addr len old (.busy commitOp (.out k)) ∧
    Found hp base addr len commitOp origin rest (.out k)

/-- Every actual post-B publication carries its owner's exact
recovered-chart tape from ISSUE3 to the old centered COMMIT.
In particular its future operand/receipt proof may work in this
one tape without moving either physical custody cut. -/
theorem actual_tour {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v)
    (hh : ∃ j,oldH6 B base j=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (mark i : Fin n)
    (pub : ¬ BStarGrantWriterHistory.NoPublication hp (run x ((u++v)++tail)) mark i) :
    CommitTour hp base x u v tail i := by
  obtain ⟨o,a,b,own,al,ab,pre,reset,post,E,A,D,R⟩ := facts.recovery hh i 1
  let rest := post++tail
  have spl : (u++v)++tail=pre++reset++rest := by rw [E]; simp only [rest,List.append_assoc]
  have keep (x : X) (w : List (Fin n)) (J : Q x) : Q (run x w) := by
    induction w generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed _ e J)
  obtain ⟨S,len,fall,C,PC,entry,m,G,_,out⟩ :=
    BStarRecoveredHistory.recovered_suffix hp R sep Q (keep _ _ I) fiber closed rest
  have ori := BStarResetSchedule.run_append step x pre reset
  let origin := run x (pre++reset)
  have old : run origin rest=run x ((u++v)++tail) := by
    exact (BStarResetSchedule.run_append step x (pre++reset) rest).symm.trans (congrArg (run x) spl.symm)
  rw [←ori] at PC entry G
  have N : Current hp base (fun j => S.getD j fall) len (run origin rest) m := by
    simpa only [origin,BStarResetSchedule.run_append] using out
  obtain ⟨k,K,loc,F,issued⟩ :=
    BStarPublicationBirth.commit_from_owner hp C sep G N mark i own (old.symm ▸ pub)
  subst m
  have last : (pre++reset).length≤(u++v).length := by
    rw [E]; simp only [List.length_append]; omega
  refine ⟨hh,o,pre,reset,rest,S,len,fall,k,spl,R,?_,?_,last,own,C,K,loc,PC,entry,G,?_,issued⟩
  · omega
  · simp only [List.length_append] at D
    omega
  · rw [←old]
    exact N

end L4.BStarReceiptRecoveredTour
