import Leader.L3.FourAgent
import Leader.L3.Headline.Proved

namespace L3

/-- **thm:main of the paper**: for every `n ≥ 5` the compiled family, and for `n = 4` the separate four-state protocol. Consumer: the L3 board (H1, H1b). -/
theorem l3MainTheorem :
    (∀ {n : Nat} (ring : DirectedRing n), 5 ≤ n → L3Headline ring) ∧
    (∀ ring : DirectedRing 4, L3FourAgentHeadline ring) :=
  ⟨fun ring hn => L3.HeadlineCleanAssembly.l3HeadlineProved ring hn,
   fun ring => l3FourAgentHeadline ring⟩

end L3

#print axioms L3.l3MainTheorem
