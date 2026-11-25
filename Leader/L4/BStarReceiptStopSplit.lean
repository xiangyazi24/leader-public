import Leader.L4.BStarReceiptKey

namespace L4.BStarReceiptStopSplit
open BStarPhysicalPairLaw BStarReceiptKey

/-- Classify the uniquely located literal read at a stop on the same tape.
A read whose mark equals the cut index belongs to the suffix. The prefix
and suffix scanners both use old prefixes from the original tape. -/
theorem at_stop {n : Nat}
    (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (key : Key n) (history future lead after : List (Fin n))
    (e : Fin n) (b : Bool)
    (cut : history++future=lead++e::after)
    (read : obs lead e=some (key,b))
    (unique : ∀ pre f post c, history++future=pre++f::post →
      obs pre f=some (key,c) → pre.length=lead.length) :
    (lead.length<history.length ∧ firstRaw obs key [] history=some b) ∨
    (history.length≤lead.length ∧ firstRaw obs key history future=some b) := by
  have hist : history <+: history++future := ⟨future,rfl⟩
  have old : lead <+: history++future := ⟨e::after,cut.symm⟩
  have marked : (lead++[e]) <+: history++future :=
    ⟨after,by simpa [List.append_assoc] using cut.symm⟩
  by_cases h : lead.length<history.length
  · refine .inl ⟨h,?_⟩
    have len : (lead++[e]).length≤history.length := by
      simp only [List.length_append,List.length_singleton]
      omega
    obtain ⟨t,T⟩ := List.prefix_of_prefix_length_le marked hist len
    have historyEq : history=lead++e::t := by
      simpa [List.append_assoc] using T.symm
    rw [historyEq]
    apply firstRaw_of_unique_position obs key [] lead t e b (by simpa using read)
    intro pre f post c split seen
    apply unique pre f (post++future) c
    · rw [historyEq,split,List.append_assoc,List.cons_append]
    · simpa using seen
  · have hle : history.length≤lead.length := by omega
    refine .inr ⟨hle,?_⟩
    obtain ⟨rel,R⟩ := List.prefix_of_prefix_length_le hist old hle
    have futureEq : future=rel++e::after := by
      apply List.append_cancel_left (as:=history)
      simpa [← List.append_assoc,R] using cut
    rw [futureEq]
    apply firstRaw_of_unique_position obs key history rel after e b
    · simpa [R] using read
    · intro pre f post c split seen
      have eq : history++future=(history++pre)++f::post := by
        rw [futureEq,split,List.append_assoc]
      have L := unique (history++pre) f post c eq seen
      rw [← R] at L
      simp only [List.length_append] at L
      omega

#print axioms at_stop
end L4.BStarReceiptStopSplit
