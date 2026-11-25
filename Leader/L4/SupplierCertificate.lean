import Leader.L4.RankSupplier

/-!
# Composing an unpaused cumulative FIFO with the fixed line path clock
The anonymous crossing-count comparison need not delay on an exposed
resident: the retained stock makes the cumulative real cuts larger.
-/

namespace L4.RankSupplier

structure PathWitness {n : Nat} (v : Fin n) (z : Virtual n) where
  L : Nat
  paths : List (List (Fin n))
  span : L ≤ 4*n
  bounded : ∀ p ∈ paths, p.length ≤ L
  count : paths.length ≤ 2^(L+1)
  complete : ∀ w,
    GGTiming.finished (GGTiming.runMarks GGTiming.advance paths w) →
      n ≤ (GGTiming.runMarks (virtualStep v) z w).departures

structure Concurrent (p c n : Nat) where
  real : Obs p c n
  queue : Virtual n
  todo : List (List (Fin n))

def concurrentStep {p c n : Nat} (v : Fin n) (q : Concurrent p c n)
    (e : Fin n) : Concurrent p c n :=
  ⟨advance v q.real e,virtualStep v q.queue e,GGTiming.advance q.todo e⟩

theorem concurrent_projects {p c n : Nat} (v : Fin n) (q : Concurrent p c n)
    (w : List (Fin n)) :
    let t := GGTiming.runMarks (concurrentStep v) q w
    t.real = track v q.real w ∧
      t.queue = GGTiming.runMarks (virtualStep v) q.queue w ∧
      t.todo = GGTiming.runMarks GGTiming.advance q.todo w := by
  induction w generalizing q with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons e w ih => exact ih (concurrentStep v q e)

def UnpausedFIFODominates {p c n : Nat} (v : Fin n) (s : Obs p c n) : Prop :=
  DepartureProjection v s
    (fun w => (GGTiming.runMarks (virtualStep v) (virtualInit v s) w).departures)

/-- The literal virtual and real clock states receive every raw mark,
including on steps where the old ghost resident is exposed. -/
def unpaused_certificate {p c n : Nat} (hn : 4 ≤ n) (v : Fin n) (s : Obs p c n)
    (h : Live v s) (clk : PathWitness v (virtualInit v s)) (fifo : UnpausedFIFODominates v s) :
    PushCertificate v s := by
  let q₀ : Concurrent p c n := ⟨s,virtualInit v s,clk.paths⟩
  refine {
    State := Concurrent p c n, start := q₀, project := Concurrent.real
    next := concurrentStep v,
    good := fun q => ∃ w, GGTiming.runMarks (concurrentStep v) q₀ w = q,
    ready := fun q => q.real.stopped = true,
    virtual := Concurrent.queue, paths := Concurrent.todo,
    paused := fun _ => False, credit := fun _ => 0, L := clk.L,
    liveStart := h, goodStart := ⟨[],rfl⟩
    keepGood := ?_, projectStart := rfl, projectStep := fun _ _ => rfl
    virtualStart := rfl, ready_iff_stop := fun _ => Iff.rfl,
    initialCredit := Nat.zero_le _, span_bound := clk.span,
    bounded_paths := clk.bounded, count_paths := clk.count,
    keepCredit := fun _ _ _ _ => Nat.le_refl _, goodLive := ?_,
    actual_domination := ?_, virtual_finishes := ?_,
    active := fun _ _ _ _ _ => ⟨rfl,rfl⟩,
    suspended := fun _ _ _ hf => hf.elim
  }
  · intro q e hq
    obtain ⟨w,rfl⟩ := hq
    exact ⟨w++[e],by rw [GGTiming.runMarks_append]; rfl⟩
  · intro q hq ht
    obtain ⟨w,rfl⟩ := hq
    have hh := (concurrent_projects v q₀ w).1
    change (GGTiming.runMarks (concurrentStep v) q₀ w).real.stopped ≠ true at ht
    rw [hh] at ht ⊢
    exact live_track hn v s w h (Bool.eq_false_iff.mpr ht)
  · intro q hq ht
    obtain ⟨w,rfl⟩ := hq
    have hh := concurrent_projects v q₀ w
    change (GGTiming.runMarks (concurrentStep v) q₀ w).real.stopped ≠ true at ht
    rw [hh.1] at ht
    change (GGTiming.runMarks (concurrentStep v) q₀ w).queue.departures ≤
      (GGTiming.runMarks (concurrentStep v) q₀ w).real.donor-s.donor
    rw [hh.1,hh.2.1]
    exact fifo w (Bool.eq_false_iff.mpr ht)
  · intro q hq _ ht
    obtain ⟨w,rfl⟩ := hq
    have hh := (concurrent_projects v q₀ w).2
    change GGTiming.finished (GGTiming.runMarks (concurrentStep v) q₀ w).todo at ht
    rw [hh.2] at ht
    change n ≤ (GGTiming.runMarks (concurrentStep v) q₀ w).queue.departures
    rw [hh.1]
    exact clk.complete w ht

end L4.RankSupplier

