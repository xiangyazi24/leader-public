import Leader.L4.BarrierProbability

namespace L4.TaggedFront

/-- Clockwise positions, measured by a modular offset. -/
def plusOffset {n : Nat} (start : Fin n) (i : Nat) : Fin n :=
  ⟨(start.val+i)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt start.isLt)⟩

/-- In a covered state the effective-root test is exactly the incoming
marker. Search responder distances 1 through n (the tag's own site is
last, not first). -/
def firstMarkedEdge {p c1 n : Nat} (x : Config p c1 n) (tag : Fin n) : Option (Fin n) :=
  (List.ofFn (fun i : Fin n => plusOffset tag i.val)).find? (fun e => (x e).mark)

def firstRoot {p c1 n : Nat} (x : Config p c1 n) (tag : Fin n) : Option (Fin n) :=
  (firstMarkedEdge x tag).map rightNeighbor

/-- Identify the current first barrier only when it is a living leader. -/
def firstLeader {p c1 n : Nat} (x : Config p c1 n) (tag : Fin n) : Option (Fin n) :=
  (firstRoot x tag).filter (fun z => (x z).leader)

/-- The Bool gap test needs no separate numerical lift: the next three
incoming bonds are unmarked, which is exactly nonrootness under MCOV. -/
def isLong {p c1 n : Nat} (x : Config p c1 n) (z : Fin n) : Bool :=
  !(x z).mark && !(x (rightNeighbor z)).mark &&
    !(x (rightNeighbor (rightNeighbor z))).mark

theorem certifiedLong {p c1 n : Nat} {x : Config p c1 n} {z : Fin n}
    (hn : 4 ≤ n) (hm : MCOV x) (hc : COV x) (hl : (x z).leader = true)
    (h : isLong x z = true) : LongBarrier x z := by
  have hmarks : (x z).mark = false ∧ (x (rightNeighbor z)).mark = false ∧
      (x (rightNeighbor (rightNeighbor z))).mark = false := by
    simpa [isLong, Bool.and_eq_true, and_assoc] using h
  exact ⟨hn, hm, hc, hl, (covered_noRoot_iff hm).2 hmarks.1,
    (covered_noRoot_iff hm).2 hmarks.2.1, (covered_noRoot_iff hm).2 hmarks.2.2⟩

end L4.TaggedFront

#print axioms L4.TaggedFront.certifiedLong
