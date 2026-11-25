import Leader.L4.OpenQueue

namespace L4.TaggedTailKernel

/-- Common denominator 7² · 8⁵ for (7/8)^d, −2 ≤ d ≤ 5. -/
def scale : Nat := 1605632

def ratioNumerator (d : Int) : Nat :=
  if d = -2 then 2097152
  else if d = -1 then 1835008
  else if d = 0 then 1605632
  else if d = 1 then 1404928
  else if d = 2 then 1229312
  else if d = 3 then 1075648
  else if d = 4 then 941192
  else if d = 5 then 823543
  else 0

/-- At most four nominatable physical marks. When the outgoing label is
itself a queue edge, the "other" entry is the baseline and can be removed.
For an outgoing edge outside the queue, "other" represents only that
outgoing edge, not all untouched marks. -/
def table (q : OpenQueue.StockPair) (out b : OpenQueue.Bond) : Nat :=
  ratioNumerator ((if out = b then 5 else 0) - OpenQueue.scaledIncrement q b)

/-- Exact four-entry local kernel: the scaled 7/8 weight loses more than
one sixth of one baseline entry after summing over the selected labels.
This is a local numerical theorem, not the global scaled-weight/tail
instantiation on all physical finite words. -/
theorem active_local_kernel (q : OpenQueue.StockPair) (out : OpenQueue.Bond) :
    6 * (table q out .inject + table q out .transfer +
      table q out .outlet + table q out .other) ≤ 23 * scale := by
  rcases q with ⟨i,j⟩
  cases i <;> cases j <;> cases out <;> decide

theorem inactive_local_kernel : 6 * ratioNumerator 5 ≤ 5 * scale := by decide

end L4.TaggedTailKernel

