import Leader.L4.BStarNativeReceiptTape

namespace L4.BStarNativeFirstSplit
open BStarLongWork BStarSeparatingRail BStarAcquireVisitOrder AllSizeProtocol BStarTrace BStarNativeReceiptTape BStarGeneratedBandScan BStarLongFixedRouting
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- On one raw word, the initial PC13 consume chronologically precedes every
positive arithmetic head's entire flight, not merely its eventual consume. -/
theorem after_first {base initial : X} {addr : Nat → Pos n} {len : Nat}
    {whole first rest prior flight tail : List (Fin n)} {firstDoor door : Fin n} {k : Nat}
    (positive : 0<k) (W0 : whole=first++firstDoor::rest)
    (W : whole=prior++(flight++door::tail))
    (F0 : Flat hp initial (addr 0).1 first)
    (H0 : Hit hp base addr len (run initial first) firstDoor 13)
    (F : Flat hp (run initial prior) (addr 0).1 flight)
    (H : Hit hp base addr len (run (run initial prior) flight) door (13+k)) :
    ∃ between, prior=first++firstDoor::between := by
  have A : (first++[firstDoor]) <+: whole := ⟨rest,by simpa [List.append_assoc] using W0.symm⟩
  have Bp : prior <+: whole := ⟨_,W.symm⟩
  have L : (first++[firstDoor]).length≤prior.length := by
    by_cases enough : (first++[firstDoor]).length≤prior.length
    · exact enough
    · have firstP : first <+: whole := ⟨_,W0.symm⟩
      obtain ⟨suffix,E⟩ := List.prefix_of_prefix_length_le Bp firstP (by simp at enough; omega)
      have a := F0 prior suffix E.symm
      have b := F0 first [] (List.append_nil _).symm
      have f := F flight [] (List.append_nil _).symm
      have p0 := H0.2.2.1
      have q := H.2.2.1
      omega
  obtain ⟨between,E⟩ := List.prefix_of_prefix_length_le A Bp L
  exact ⟨between,by simpa [List.append_assoc] using E.symm⟩

#print axioms after_first
end L4.BStarNativeFirstSplit
