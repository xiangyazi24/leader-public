import Leader.L4.ShortFiveWatchReplay
import Leader.L4.ShortGuardedNOR

namespace L4.ShortFivePairClassifier
open PhysicalCustody ShortGuardedNOR ShortFiveWatchReplay ShortResetCycle
open ShortSimulLocal (Fiber)
open ShortResetMIS1Ring (header)

/-- Only the two covered old MIS1 bytes, the frozen lower mask, and
the resulting covered selector bit are used. No claim about other
sheets at either physical endpoint is needed. -/
theorem pair_local {s n : Nat} {h : Fin n→Bool} (cs : Fin 5→Chart h)
    (x y : Raw s n) (e : Fin n)
    (X : Fiber h x) (Y : Fiber h y) (A : Agree cs x y)
    (I : Internal cs e) :
    classifyFixed h x e=classifyFixed h y e := by
  have K := internal_step_agrees cs x y X Y A e I
  have O := A (rightNeighbor e) I.2
  have P := K (rightNeighbor e) I.2
  have H : header x (rightNeighbor e)=header y (rightNeighbor e) :=
    (X.2 _).trans (Y.2 _).symm
  unfold classifyFixed ShortPublicationClassifier.classify
  dsimp only
  rw [O,P,H]

theorem matched_publication_real {s n : Nat} {h : Fin n→Bool}
    (cs : Fin 5→Chart h) (N : 5≤n) (x : Raw s n)
    (X : Fiber h x) (w t : List (Fin n)) (M : keep cs w=t)
    (I : ∀ e∈t,Internal cs e) (i : Sites h)
    (E : i∈ShortNORCover.publications (rawNext s) (classifyFixed h) x t) :
    i∈ShortNORCover.publications (rawNext s) (classifyFixed h) x w :=
  publication_on_original_word cs N (classifyFixed h)
    (fun x y e X Y A I => pair_local cs x y e X Y A I)
    x x X X (fun _ _=>rfl) w t M I i E

#print axioms pair_local
#print axioms matched_publication_real
end L4.ShortFivePairClassifier
