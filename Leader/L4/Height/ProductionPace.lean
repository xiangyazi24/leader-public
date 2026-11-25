import Leader.L4.Height.ProductionAdmissions
import Leader.L4.Height.AdmissionMask
import Leader.L4.BStarFiveClientBudget

namespace L4.Height.ProductionPace
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner
open BStarLongFixedRouting BStarPaceCount BStarPaceBetweenCharge BStarPaceSteeredCharge
open BStarSteeredLikelihood BStarSteeringSupport BStarFiveClientBudget
open BStarParkedSteering BStarClearanceRaceMark BStarLongClaims
open Classical
noncomputable section

private theorem emit_snoc {n : Nat} (c : Word n → Fin n → Fin n) (a u : Word n) (e : Fin n) :
    emit c a (u++[e])=emit c a u ++ [c (a++emit c a u) e] := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons b u ih => simp only [List.cons_append,emit,ih,List.append_assoc,List.nil_append,List.cons_append]

private theorem played_eq {n : Nat} (R : Word n → Fin n → Option (Fin n)) (a w : Word n) :
    let out := emit (chooseBy R) []
    playedWord (fun b => R (out b)) a w = emit (chooseBy R) (out a) w := by
  dsimp only
  induction w generalizing a with
  | nil => rfl
  | cons e w ih => simp only [playedWord,emit,ih,emit_snoc,List.nil_append,chooseBy]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

theorem owner_excess_mass {base ini : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ b j,Layout B base j=Layout B (run ini b) j)
    (actual : ∀ w, ∃ m d, GeneratedOwner hp base (fun j=>S.getD j fall) len ini m w d)
    (W : Nat) (ratio : 4*W≤81*len) (pos : 0<len) (hn : 0<n)
    (R : Word n → Fin n → Option (Fin n)) (support : ∀ a, Supported _ hh (R a)) :
    let t := 2*(2^20*n*W)
    wordSum (fun w => ProductionAdmissions.count hp ini (S.getD 0 fall).1 []
      (emit (chooseBy R) [] w)-1) t ≤ (81*2^20)*n^t := by
  let out := emit (chooseBy R) []
  let red := fun a => R (out a)
  have compat (a : Word n) (e : Fin n) : out (a++[e])=out a++[(red a e).getD e] := by
    simpa only [out,red,chooseBy,List.nil_append] using emit_snoc (chooseBy R) [] a e
  apply excess_mass_of_charge_mass hn pos ratio []
    (candidateCharge hp base ini (fun j=>S.getD j fall) len out red) _
  · exact candidate_mass hp base ini _ _ _ hh out red (fun a => support (out a)) []
  · intro w _
    rw [charges_candidate_eq hp base ini _ _ out red compat,played_eq R [] w]
    obtain ⟨m,d,G⟩ := actual (out w)
    exact ProductionAdmissions.all_launch_excess hp C sep layout [] (out w) G

/-- At most five monitored gates may spend launch credits. Their charts can
coincide when opposite offsets identify the same owner. -/
theorem five_client_overflow {base ini : X} {hh : ∃ i,oldH6 B base i=true}
    (owner : Fin 5 → Owners (oldH6 B base)) (S : Fin 5 → List (Pos n))
    (len : Fin 5 → Nat) (fall : Fin 5 → Pos n)
    (chart : ∀ j, Chart hp base hh (owner j) (S j) (len j) (fall j))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ b i,Layout B base i=Layout B (run ini b) i)
    (actual : ∀ j w, ∃ m d, GeneratedOwner hp base (fun k=>(S j).getD k (fall j)) (len j) ini m w d)
    (W : Nat) (ratio : ∀ j,4*W≤81*len j) (pos : ∀ j,0<len j) (hn : 0<n)
    (gate : Fin 5 → Fin n) (live : Fin 5 → Word n → Prop) (pick : Word n → Fin n → Side) :
    let issue := fun j => ProductionAdmissions.issues hp ini ((S j).getD 0 (fall j)).1
    let R := AdmissionMask.mask _ hh gate issue live pick
    let t := 2*(2^20*n*W)
    8*wordSum (BStarRawBlockDrift.massInd (fun v =>
      5*2^32 < decisions (prescribed R) [] (emit (chooseBy R) [] v))) t ≤ n^t := by
  let issue := fun j => ProductionAdmissions.issues hp ini ((S j).getD 0 (fall j)).1
  let R := AdmissionMask.mask _ hh gate issue live pick
  let out := emit (chooseBy R) []
  let client := fun j v =>
    ProductionAdmissions.count hp ini ((S j).getD 0 (fall j)).1 [] (out v)-1
  have support : ∀ a, Supported _ hh (R a) := support_of_fresh (redirectTo_isFresh _ hh _ pick)
  apply overflow_of_excess _ client
  · intro j
    exact owner_excess_mass hp (chart j) sep layout (actual j) W (ratio j) (pos j) hn R support
  · intro w
    exact AdmissionMask.decisions_le_issues _ hh gate issue live pick (out w)

#print axioms owner_excess_mass
#print axioms five_client_overflow
end
end L4.Height.ProductionPace

