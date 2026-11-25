import Leader.L4.BarrierIID
import Leader.L4.TaggedTail
import Leader.L4.TaggedTailKernel

namespace L4.PhysicalTailKernel

open BarrierIID TaggedTail TaggedTailKernel

private theorem sumSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun e : Fin n => f e.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sumConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n * a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sumSucc, ih, Nat.succ_mul, Nat.add_comm]

private theorem sumAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumSucc, sumSucc f, sumSucc g, ih]; omega

private theorem sumSelector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sumSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by
        funext e
        simp [Fin.succ_ne_zero]
      rw [hz, sumConst]
      simp
    · rw [sumSucc]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

private theorem sumReplace {n : Nat} (f : Fin n → Nat) (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else f e) + f i = sumEdge f + a := by
  calc
    _ = sumEdge (fun e => (if e = i then a else f e) + (if e = i then f i else 0)) := by
      rw [sumAdd, sumSelector]
    _ = sumEdge (fun e => f e + (if e = i then a else 0)) := by
      congr 1
      funext e
      by_cases h : e = i <;> simp [h, Nat.add_comm]
    _ = _ := by rw [sumAdd, sumSelector]

private theorem bondInject {n : Nat} (b : QueueBonds n) (e : Fin n) :
    b.bond e = .inject ↔ e = b.inject := by
  by_cases hi : e = b.inject
  · simp [QueueBonds.bond, hi]
  · by_cases ht : e = b.transfer
    · simp [QueueBonds.bond, ht, Ne.symm b.inject_ne_transfer]
    · by_cases ho : e = b.outlet <;> simp [QueueBonds.bond, hi, ht, ho, Ne.symm b.inject_ne_outlet, Ne.symm b.transfer_ne_outlet]

private theorem bondTransfer {n : Nat} (b : QueueBonds n) (e : Fin n) :
    b.bond e = .transfer ↔ e = b.transfer := by
  by_cases hi : e = b.inject
  · subst e
    simp [QueueBonds.bond, b.inject_ne_transfer]
  · by_cases ht : e = b.transfer
    · simp [QueueBonds.bond, ht, Ne.symm b.inject_ne_transfer]
    · by_cases ho : e = b.outlet <;> simp [QueueBonds.bond, hi, ht, ho, Ne.symm b.inject_ne_outlet, Ne.symm b.transfer_ne_outlet]

private theorem bondOutlet {n : Nat} (b : QueueBonds n) (e : Fin n) :
    b.bond e = .outlet ↔ e = b.outlet := by
  by_cases hi : e = b.inject
  · subst e
    simp [QueueBonds.bond, b.inject_ne_outlet]
  · by_cases ht : e = b.transfer
    · subst e
      simp [QueueBonds.bond, Ne.symm b.inject_ne_transfer, b.transfer_ne_outlet]
    · by_cases ho : e = b.outlet <;> simp [QueueBonds.bond, hi, ht, ho, Ne.symm b.inject_ne_outlet, Ne.symm b.transfer_ne_outlet]

private theorem namedBondMatch {n : Nat} (b : QueueBonds n) (out e : Fin n)
    (h : b.bond e ≠ .other) :
    e = out ↔ b.bond out = b.bond e := by
  constructor
  · intro h'
    cases h'
    rfl
  · intro he
    cases hk : b.bond e with
    | inject =>
      rw [hk] at he
      exact ((bondInject b e).mp hk).trans ((bondInject b out).mp he).symm
    | transfer =>
      rw [hk] at he
      exact ((bondTransfer b e).mp hk).trans ((bondTransfer b out).mp he).symm
    | outlet =>
      rw [hk] at he
      exact ((bondOutlet b e).mp hk).trans ((bondOutlet b out).mp he).symm
    | other => exact False.elim (h hk)

private def onThree {n : Nat} (b : QueueBonds n) (w : OpenQueue.Bond → Nat)
    (e : Fin n) : Nat :=
  match b.bond e with
  | .other => scale
  | a => w a

private theorem sumThree {n : Nat} (b : QueueBonds n) (w : OpenQueue.Bond → Nat) :
    sumEdge (onThree b w) + 3 * scale =
      n * scale + w .inject + w .transfer + w .outlet := by
  let base := fun _ : Fin n => scale
  let a := fun e => if e = b.outlet then w .outlet else base e
  let d := fun e => if e = b.transfer then w .transfer else a e
  let f := fun e => if e = b.inject then w .inject else d e
  have hF : onThree b w = f := by
    funext e
    unfold onThree QueueBonds.bond
    by_cases hi : e = b.inject
    · simp [f, hi]
    · by_cases ht : e = b.transfer
      · simp [f, d, ht, Ne.symm b.inject_ne_transfer]
      · by_cases ho : e = b.outlet <;> simp [f, hi, d, ht, a, ho, base, Ne.symm b.inject_ne_outlet, Ne.symm b.transfer_ne_outlet]
  have h₀ : sumEdge a + scale = n * scale + w .outlet := by
    simpa only [a, base, sumConst] using sumReplace base b.outlet (w .outlet)
  have h₁ : sumEdge d + scale = sumEdge a + w .transfer := by
    simpa only [d, a, if_neg b.transfer_ne_outlet, base] using
      sumReplace a b.transfer (w .transfer)
  have h₂ : sumEdge f + scale = sumEdge d + w .inject := by
    simpa only [f, d, a, if_neg b.inject_ne_transfer, if_neg b.inject_ne_outlet, base] using
      sumReplace d b.inject (w .inject)
  rw [hF]
  omega

/-- Exact full raw-edge sum in the active case. The fourth slot is the
extra outgoing edge when it is outside the queue; when it overlaps an
actual queue edge, the fourth entry is a baseline rather than a second mark. -/
theorem active_sum {n : Nat} (out : Fin n) (b : QueueBonds n) (q : OpenQueue.StockPair) :
    sumEdge (fun e => ratioNumerator (driftMark out (some (b,q)) e)) + 4 * scale =
      n * scale + table q (b.bond out) .inject + table q (b.bond out) .transfer +
        table q (b.bond out) .outlet + table q (b.bond out) .other := by
  let w := table q (b.bond out)
  let f := fun e => ratioNumerator (driftMark out (some (b,q)) e)
  have named : ∀ e, b.bond e ≠ .other → f e = onThree b w e := by
    intro e h
    rw [show f e = ratioNumerator ((if e = out then 5 else 0) - OpenQueue.scaledIncrement q (b.bond e)) by rfl]
    have hbTable : onThree b w e = w (b.bond e) := by
      unfold onThree
      cases hk : b.bond e with
      | other => exact False.elim (h hk)
      | _ => rfl
    rw [hbTable]
    unfold w table
    by_cases he : e = out
    · simp [he]
    · have hn : b.bond out ≠ b.bond e := fun eq => he ((namedBondMatch b out e h).mpr eq)
      simp [he, hn]
  have h₃ := sumThree b w
  change sumEdge f + 4 * scale = n * scale + w .inject + w .transfer + w .outlet + w .other
  by_cases hO : b.bond out = .other
  · let f' := fun e => if e = out then w .other else onThree b w e
    have hEq : f = f' := by
      funext e
      by_cases he : e = out
      · subst e
        simp [f, f', w, hO, driftMark, queueMark, table]
      · by_cases hb : b.bond e = .other
        · simp [f, f', onThree, he, hb, driftMark, queueMark,
            OpenQueue.scaledIncrement_other, ratioNumerator, scale]
        · simpa [f', he] using named e hb
    have h₄ : sumEdge f' + scale = sumEdge (onThree b w) + w .other := by
      simpa [f', onThree, hO] using sumReplace (onThree b w) out (w .other)
    rw [hEq]
    omega
  · have hEq : f = onThree b w := by
      funext e
      by_cases hb : b.bond e = .other
      · have hne : e ≠ out := by
          intro h
          subst e
          exact hO hb
        simp [f, onThree, hne, hb, driftMark, queueMark, OpenQueue.scaledIncrement_other,
          ratioNumerator, scale]
      · exact named e hb
    have hb : w .other = scale := by
      simp [w, table, hO, OpenQueue.scaledIncrement_other, ratioNumerator, scale]
    rw [hEq, hb]
    omega

/-- Exact full raw-edge sum when there is no active ideal queue. -/
theorem inactive_sum {n : Nat} (out : Fin n) :
    sumEdge (fun e => ratioNumerator (driftMark out none e)) + scale =
      n * scale + ratioNumerator 5 := by
  have h := sumReplace (fun _ : Fin n => scale) out (ratioNumerator 5)
  rw [sumConst] at h
  have hc : (fun e => ratioNumerator (driftMark out none e)) =
      (fun e => if e = out then ratioNumerator 5 else scale) := by
    funext e
    by_cases he : e = out <;> simp [he, driftMark, queueMark, ratioNumerator, scale]
  rw [hc]
  exact h

/-- Exact normalized one-mark exponential contraction over all actual
physical directed edges, also when the tag outgoing mark is a queue mark. -/
theorem drift_kernel {n : Nat} (hn : 4 ≤ n) (out : Fin n)
    (queue : Option (QueueBonds n × OpenQueue.StockPair)) :
    6 * sumEdge (fun e => ratioNumerator (driftMark out queue e)) ≤
      (6 * n - 1) * scale := by
  cases queue with
  | none =>
    have h₁ := inactive_sum out
    have h₂ := inactive_local_kernel
    unfold scale at *
    omega
  | some bq =>
    rcases bq with ⟨b,q⟩
    have h₁ := active_sum out b q
    have h₂ := active_local_kernel q (b.bond out)
    unfold scale at *
    omega

end L4.PhysicalTailKernel

#print axioms L4.PhysicalTailKernel.active_sum
#print axioms L4.PhysicalTailKernel.inactive_sum
#print axioms L4.PhysicalTailKernel.drift_kernel
