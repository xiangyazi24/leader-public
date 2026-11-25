import Leader.L4.WindowForeignWitness
import Leader.L4.WindowLocal

namespace L4.WindowA0ForeignBirth
open RankPhysical RootedAssembly SevenTagCharge

/-- A foreign birth in the rightmost exterior head is not an A0
exit; the original seven IDs still occupy their old slots. -/
def tape : Config 2 12 40 := fun i =>
  { WindowForeignWitness.tape i with
    leader := false
    bullet := .none
    shield := false
    source := if i.val=15 then .await 23 else .off
    rail := if i.val=14 then .dc else .e }

theorem quiet : QuietEntrance tape := by
  refine ⟨?_,?_,⟨0,rfl⟩,?_⟩
  · unfold MCOV; decide
  · unfold COV; decide
  · intro b hb; cases hb

def first : Fin (rank tape) := ⟨0,by decide⟩

theorem exterior_birth_is_not_A0_exit :
    rank tape = 8 ∧
    2*WindowSpan.span tape first+2<40 ∧
    window7 (WindowRoster.roster tape) first=[0,2,4,6,8,10,12] ∧
    (tape 3).leader=false ∧ (tape 5).leader=false ∧
    (step tape 14 3).leader=false ∧ (step tape 14 5).leader=false ∧
    (step tape 14 15).leader=true ∧
    WindowLocal.route [0,2,4,6,8,10,12] [] (some 2) (initial tape) 14=.keep ∧
    WindowLocal.route [0,2,4,6,8,10,12] [] (some 4) (initial tape) 14=.keep ∧
    reward tape (window7 (WindowRoster.roster tape) first) [14]=0 := by
  decide

#print axioms quiet
#print axioms exterior_birth_is_not_A0_exit
end L4.WindowA0ForeignBirth
