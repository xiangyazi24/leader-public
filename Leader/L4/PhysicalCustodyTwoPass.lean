import Leader.L4.PhysicalCustodyCommonReplay
import Leader.L4.PhysicalCustodySampledPass

namespace L4.PhysicalCustody
open BStarTrace BStarH6WordChart BStarAcquireLiteralChain BStarAcquireAnchors
open BStarOwnerRecoveryPass PhysicalCustodySampledPass
local notation "hp" => (show 0<2 by decide)
set_option maxRecDepth 4096

def ownerOrder {n : Nat} (h : Fin n → Bool) : List (Owners h) :=
  List.ofFn (fun j : Fin (total h) => ⟨(j.val : Int), by omega, by omega⟩)

theorem ownerOrder_ports {n : Nat} (h : Fin n → Bool) (hh : ∃ i, h i = true)
    (i : Fin n) (j : Fin 3) :
    ∃ o ∈ ownerOrder h, commandOwner h i (BStarResetNoAcquire.slot j) = o.val := by
  let a := commandOwner h i (BStarResetNoAcquire.slot j)
  have r : 0≤a ∧ a<(total h : Int) := commandOwner_range h hh i _
  let f : Fin (total h) := ⟨a.toNat,by omega⟩
  refine ⟨⟨(f.val : Int),by omega,by omega⟩,List.mem_ofFn.mpr ⟨f,rfl⟩,?_⟩
  change a=(a.toNat : Int)
  omega

/-- A local sampled segment may have a replay tail following its genuine
Recovered subword. The final disjoint wait is retained in the word and is
not mislabeled as part of the authenticated recovery. -/
def HoldsCredit {s n : Nat} {Owner : Type} (E : Owner → Raw s n → List (Fin n) → Prop)
    (o : Owner) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ a b, a<b ∧ BStarRecoveryPass.Credit (rawNext s) E o x w a b

theorem flatten_pass_credits {s n : Nat} {Owner : Type}
    {E : Owner → Raw s n → List (Fin n) → Prop} {x : Raw s n}
    {owners : List Owner} {u v : List (Fin n)}
    (P : Pass (HoldsCredit E) x owners u v) :
    Commuted u v ∧ ∀ o∈owners, HoldsCredit E o x v := by
  induction P with
  | nil x => exact ⟨.refl _, by simp⟩
  | @cons x o os a b u v commute _ H _ ih =>
    refine ⟨PhysicalCustodyCommonWord.commute_append commute ih.1, ?_⟩
    intro p mem
    rcases List.mem_cons.mp mem with rfl|mem
    · obtain ⟨j,k,lt,credit⟩ := H
      exact ⟨j,k,lt,BStarRecoveryPass.credit_append (rawNext s) credit v⟩
    · obtain ⟨j,k,lt,credit⟩ := ih.2 p mem
      rw [rawRun_of_commuted x commute] at credit
      exact ⟨b.length+j,b.length+k,by omega,BStarRecoveryPass.credit_shift (rawNext s) b credit⟩

/-- A single authentication word suffices for both custody cuts. The two
passes must start at the actual sampled endpoints and cannot swap marks
across the cut. Every physical port is covered by the owner order. -/
theorem custody_of_two_sampled_passes {s n : Nat} {z : Raw s n}
    (g : ReadyAfterCovers z) {u v u' v' : List (Fin n)}
    (A : Pass (Recovered hp z g.hh) z (ownerOrder (oldH6 (rows s) z)) u u')
    (B : Pass (Recovered hp z g.hh) (rawRun z u) (ownerOrder (oldH6 (rows s) z)) v v') :
    Custody (rawRun z (u++v)) := by
  obtain ⟨_,_,first,second⟩ := two_sampled_passes [] A B
  simp only [List.append_nil] at first second
  have cuts := PhysicalCustodyCreditCuts.cuts_of_credits hp g.hh g.sep
    g.Q g.qz g.closed g.fiber (ownerOrder (oldH6 (rows s) z)) (ownerOrder_ports _ g.hh) u' v'
    first (fun o member => by
      obtain ⟨a,b,lower,lt,_,credit⟩ := second o member
      exact ⟨a,b,lower,lt,credit⟩)
  exact common_replay_implies_custody g ⟨u,v,u',v',rfl,(one_pass A).1,(one_pass B).1,cuts⟩

/-- Custody from two authenticated sampled passes, allowing a local replay
to retain irrelevant marks after the terminal consume. -/
theorem custody_of_two_credited_passes {s n : Nat} {z : Raw s n}
    (g : ReadyAfterCovers z) {u v u' v' : List (Fin n)}
    (A : Pass (HoldsCredit (Recovered hp z g.hh)) z (ownerOrder (oldH6 (rows s) z)) u u')
    (B : Pass (HoldsCredit (Recovered hp z g.hh)) (rawRun z u) (ownerOrder (oldH6 (rows s) z)) v v') :
    Custody (rawRun z (u++v)) := by
  obtain ⟨cu,firstLocal⟩ := flatten_pass_credits A
  obtain ⟨cv,secondLocal⟩ := flatten_pass_credits B
  obtain ⟨_,_,first,second⟩ := PhysicalCustodyCommonWord.replay_two_passes z _ u v u' v' []
    cu cv (Recovered hp z g.hh) (Recovered hp z g.hh) firstLocal secondLocal
  simp only [List.append_nil] at first second
  have cuts := PhysicalCustodyCreditCuts.cuts_of_credits hp g.hh g.sep
    g.Q g.qz g.closed g.fiber (ownerOrder (oldH6 (rows s) z)) (ownerOrder_ports _ g.hh) u' v'
    first (fun o member => by
      obtain ⟨a,b,lower,lt,_,credit⟩ := second o member
      exact ⟨a,b,lower,lt,credit⟩)
  exact common_replay_implies_custody g ⟨u,v,u',v',rfl,cu,cv,cuts⟩

end L4.PhysicalCustody
