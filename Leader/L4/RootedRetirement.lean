import Leader.L4.RootedAssembly
import Leader.L4.TripleBoundary

namespace L4.RootedRetirement
open TaggedTail RankPhysical RootedAssembly Classical

def RootedRetirementBlock : Prop :=
  ∀ c : Nat, 12≤c → ∃ B : Nat, 0<B ∧
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n → QuietEntrance x → 2≤rank x →
      2*survival step (fun y => rank x≤rank y) (B*n^2) x≤n^(B*n^2)

theorem boundedRank_of_block (h : RootedRetirementBlock) : RootedBoundedRank := by
  intro c hc
  obtain ⟨B,hB,htrial⟩ := h c hc
  refine ⟨2*B, ?_⟩
  intro p n x hp hn hx hr
  let R := rank x
  let State := {y : Config p c n // QuietEntrance y ∧ rank y ≤ R}
  let lift (y : State) (e : Fin n) : State :=
    ⟨step y.val e, RootedFresh.quiet_step _ _ hp hc hn y.property.1,
      Nat.le_trans (rank_step_le hn _ e y.property.1.1) y.property.2⟩
  let flag (y : State) : Nat := if rank y.val < R then 0 else 1
  let start : State := ⟨x, hx, Nat.le_refl _⟩
  have hflag (y : State) : flag y ≤ 1 := by unfold flag; split <;> omega
  have hmono (y : State) (e : Fin n) : flag (lift y e) ≤ flag y := by
    have hr' := rank_step_le hn y.val e y.property.1.1
    by_cases h : rank y.val < R
    · have hh : rank (lift y e).val < R := Nat.lt_of_le_of_lt hr' h
      simp [flag,h,hh]
    · simpa [flag,h] using hflag (lift y e)
  have hL : 0 < B*n^2 := Nat.mul_pos hB (Nat.pow_pos (by omega))
  have hprob (y : State) (hy : 0 < flag y) :
      2 * survival lift (fun z => flag y ≤ flag z) (B*n^2) y ≤ (2-1)*n^(B*n^2) := by
    have hfy : flag y = 1 := by have := hflag y; omega
    have hge : R ≤ rank y.val := by
      by_cases he : rank y.val < R
      · simp [flag,he] at hy
      · omega
    have heq := Nat.le_antisymm y.property.2 hge
    have hlive : (fun z : State => flag y ≤ flag z) =
        (fun z : State => rank y.val ≤ rank z.val) := by
      funext z; apply propext
      rw [hfy,heq]
      change (1 ≤ (if rank z.val < R then 0 else 1)) ↔ R ≤ rank z.val
      by_cases hz : rank z.val < R <;> simp [hz] <;> omega
    rw [hlive]
    have hh := equal_survival_of_projection step lift (fun z => rank y.val ≤ rank z)
      (fun z : State => z.val) (fun _ _ => rfl) (B*n^2) y
    rw [hh]
    have hr' : 2 ≤ rank y.val := by rw [heq]; exact hr
    simpa using htrial y.val hp hn y.property.1 hr'
  have hcost := RankRenewal.expected_of_rank_trial_certificate (next := lift)
    flag (fun y : State => rank y.val < R)
    (fun y h => by
      by_cases h' : rank y.val < R
      · exact h'
      · simp [flag,h'] at h)
    hmono (B*n^2) 2 1 hL (by decide) hprob start (hflag start)
  intro t
  have hpj := EntranceCover.iidHitCost_le_of_projection step lift
    (fun y => rank y < R) (fun y : State => rank y.val < R)
    (fun y : State => y.val) (fun _ _ => rfl) (fun _ h => h) t start
  refine Nat.le_trans hpj ?_
  have hc' := hcost t
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_one,Nat.one_mul] using hc'

theorem block_of_restartTrial (h : RestartSerial.RootIndependentRestartTrial) : RootedRetirementBlock := by
  intro c hc
  obtain ⟨A,hA,hcert⟩ := h c hc
  refine ⟨4*A,by omega,?_⟩
  intro p n x hp hn hx hr
  obtain ⟨C⟩ := hcert x hp hn hx hr
  let live := fun y : C.State => rank x ≤ rank (C.project y)
  have hLive (y : C.State) (e : Fin n) (h : live (C.next y e)) : live y := by
    unfold live at h ⊢
    rw [C.projectStep] at h
    exact Nat.le_trans h (rank_step_le hn _ e (C.quiet y).1)
  have hK : 0<A*n^2 := Nat.mul_pos hA (Nat.pow_pos (by omega))
  have hh := halfBlock_of_stopped_attempt C.next live C.done C.failed hLive
    C.doneAbsorbs C.terminalFailure (A*n^2) hK C.start C.mean C.failureMass
  unfold live at hh
  rw [equal_survival_of_projection step C.next (fun y => rank x ≤ rank y)
    C.project C.projectStep, C.initial] at hh
  simpa only [Nat.mul_assoc] using hh

theorem boundedRank_of_restartTrial (h : RestartSerial.RootIndependentRestartTrial) : RootedBoundedRank :=
  boundedRank_of_block (block_of_restartTrial h)

theorem rootedBoundedRank_of_boundary (h : TripleBoundary.MissingBoundary) :
    RootedBoundedRank :=
  boundedRank_of_restartTrial (TripleBoundary.restartTrial_of_boundary h)

theorem uniformEdge_rooted_of_boundary (h : TripleBoundary.MissingBoundary)
    (windows : RootedWindowMarginals) : RootedStatement :=
  uniformEdge_rooted (rootedBoundedRank_of_boundary h) windows

end L4.RootedRetirement

