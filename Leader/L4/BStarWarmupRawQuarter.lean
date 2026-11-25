import Leader.L4.BStarPhysicalCompletion
import Leader.L4.BStarWarmupQuarter

namespace L4.BStarWarmupRawQuarter
open BStarWarmupQuarter BStarPhysicalCompletion BStarPhysicalPairLaw
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart L4.Height
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- A uniform logical quarter bound pulls back through a random opening
slice when the deterministic comparison uses disjoint warm-up and main
coordinates. Neither chronological reveal order nor physical coverage of
unused coordinates is assumed. -/
theorem raw_warmup_quarter {A K : Nat} {Slice : Type}
    (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (initialTime : Fin n→Nat) (history : List (Fin n)) (t : Nat)
    (coord : Key n→Option (Fin (A+K))) (key : Fin (A+K)→Key n)
    (fiber : ∀ k j, coord j=some k ↔ j=key k)
    (E : List (Fin n)→Prop) (slice : Bits A→Slice)
    (F : Slice→Bits K→Prop) (bad : Slice→List (Bits K))
    (exactBad : ∀ s b,b∈bad s ↔ F s b)
    (distinct : ∀ s,(bad s).Nodup) (quarter : ∀ s,4*(bad s).length≤2^K)
    (compare : ∀ u, u.length=t → E u → ∀ a : Bits (A+K),
      (∀ k b, firstRaw (reveal hp base hh x (ownerAt hp base hh) initialTime)
        (key k) history u=some b → a k=b) →
      F (slice (warm (K:=K) a)) (main (A:=A) a)) :
    4*wordSum (fun u=>if E u then 1 else 0) t≤n^t := by
  obtain ⟨badVec,nd,exactVec,quarterVec⟩ := enumerate_bad slice bad F exactBad distinct quarter
  exact raw_quarter_of_compatible hp base x hh initialTime history t coord key fiber E
    (fun a=>F (slice (warm (K:=K) a)) (main (A:=A) a))
    badVec nd exactVec quarterVec compare

end L4.BStarWarmupRawQuarter
