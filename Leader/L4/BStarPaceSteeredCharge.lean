import Leader.L4.BStarPaceChartLedger
import Leader.L4.BStarSteeringSupport

namespace L4.BStarPaceSteeredCharge
open AllSizeProtocol BStarTrace BStarLongWork
open BStarAcquireVisitOrder BStarH6WordChart
open BStarPaceChartLedger BStarPaceCount BStarSteeringSupport Height
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

noncomputable def candidateCharge (base initial : X) (addr : Nat→Pos n) (len : Nat)
    (played : List (Fin n)→List (Fin n))
    (redirect : List (Fin n)→Fin n→Option (Fin n))
    (a : List (Fin n)) (e : Fin n) : Nat :=
  rawCharge hp base initial addr len (played a) ((redirect a e).getD e)

/-- Even after predictable same-category redirection, a literal
outward PACE nomination has at most two contributing candidate labels.
The played physical history can depend on every earlier candidate;
no future mark is supplied to that map. -/
theorem candidate_mass (base initial : X) (addr : Nat→Pos n) (len : Nat)
    (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (played : List (Fin n)→List (Fin n))
    (redirect : List (Fin n)→Fin n→Option (Fin n))
    (support : ∀ a, Supported h hh (redirect a))
    (a : List (Fin n)) (t : Nat) :
    n*wordSum (charges (candidateCharge hp base initial addr len played redirect) a) t ≤
      2*t*n^t := by
  let f := rawCharge hp base initial addr len
  let nom : List (Fin n)→Fin n := fun p=>
    if H : ∃ e,0<f (played p) e then Classical.choose H else (addr 0).1
  apply departure_mass redirect nom _ (fun a=>partial_injective (support a))
  · intro p e
    unfold candidateCharge rawCharge
    split <;> omega
  · intro p e positive
    let z := (redirect p e).getD e
    change 0<f (played p) z at positive
    have H : ∃ j,0<f (played p) j := ⟨z,positive⟩
    exact (rawCharge_unique hp base initial addr len (played p)
      z (Classical.choose H) positive (Classical.choose_spec H)).trans
        (by unfold nom; rw [dif_pos H])

#print axioms candidate_mass
end L4.BStarPaceSteeredCharge

