import Leader.L4.WindowCappedMean
import Leader.L4.PhysicalPublic
import Leader.L4.MonitorRawBridge

namespace L4.WindowCappedRetirement
open TaggedTail RankPhysical RootedAssembly Classical

theorem block_at {p c n : Nat} (x : Config p c n) (hp : 2≤p) (hc : 12≤c)
    (hn : 4≤n) (hx : QuietEntrance x) (hr : 2≤rank x) :
    2*survival step (fun y => rank x≤rank y) (4*RestartSerial.verifiedAttempt c*n^2) x
      ≤ n^(4*RestartSerial.verifiedAttempt c*n^2) := by
  let A := RestartSerial.verifiedAttempt c
  have hA : 0<A := (RestartSerial.verifiedAttempt_calibrate c).1
  let clock : TripleResidual.ConcreteTripleSharpClock := TripleAssembly.sharp_clock_of_physical_stageB
    (TripleBoundary.physicalStageB_of_boundary G6Complete.boundary)
  let C := (RestartClosure.observerOfTripleClock x hx hr ⟨hp,hc,hn,hr⟩ clock).toRestartTrial
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

theorem bounded_at (c : Nat) (hc : 12≤c) :
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n → QuietEntrance x → 2≤rank x →
      IIDExpectedHittingTimeAtMost step (fun y => rank y<rank x) x
        ((2*(4*RestartSerial.verifiedAttempt c))*n^2) := by
  let B := 4*RestartSerial.verifiedAttempt c
  have hB : 0<B := Nat.mul_pos (by decide) (RestartSerial.verifiedAttempt_calibrate c).1
  have htrial {p n : Nat} (x : Config p c n) (hp : 2≤p) (hn : 4≤n)
      (hx : QuietEntrance x) (hr : 2≤rank x) :
      2*survival step (fun y => rank x≤rank y) (B*n^2) x≤n^(B*n^2) :=
    block_at x hp hc hn hx hr
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

end L4.WindowCappedRetirement

namespace L4.WindowCappedPublic
open TaggedTail RankRenewal RankPhysical TripleRenewal Classical RankBlockContraction SevenTagCharge
open RootedAssembly WindowSpan

open BoundedPublicCodec WindowCappedMean
set_option exponentiation.threshold 512

def retirement : Nat := 2*(4*RestartSerial.verifiedAttempt 12)
def window : Nat := windowCoeff 12 boundedN
def patrol := 512*window + 480*retirement + 1617
def coefficient := 2049 + patrol

theorem retirement_eq : retirement = 36712 := by decide
theorem coefficient_lt : coefficient < 2^58 := by decide
theorem coefficient_eq : coefficient = 151715012464800082 := by decide

private theorem marginal :
    ∀ (n L : Nat), 4≤n → n≤boundedN → 1≤L → L≤n →
    ∃ H : Nat, H*L≤60*n ∧ ∀ {p : Nat} (x : Config p 12 n), 2≤p → QuietEntrance x →
      Nonempty (WindowMarginals x H ((2*window)*n*L)) := by
  let B := window
  intro n L hn hN hL hnL
  let D := shortSpanCutoff n L
  let H := 6*n/D
  let T := (2*B)*n*L
  have cut := shortSpanCutoff_bounds n L hn hL hnL
  change 0<D ∧ D+1≤2*L ∧ (5≤n → 2*D+2<n) ∧ L≤10*D at cut
  refine ⟨H,shortSpanOffset_budget n L hn hL hnL,?_⟩
  intro p x hp hq
  by_cases hk : 7≤rank x
  · have h5 : 5≤n := by have hb := rank_le_size x; omega
    refine ⟨{ k := rank x
              roster := WindowRoster.roster x
              inj := WindowRoster.roster_injective x
              starts := shortStarts x D
              nodup := shortStarts_nodup x D
              many := shortStarts_many x D cut.1
              trial := ?_ }⟩
    intro i hi
    have hs : span x i≤D := of_decide_eq_true (List.mem_filter.mp hi).2
    have hlocal' := capped_reward hp (by decide) hn x hq i hk boundedN hN
      (by have := cut.2.2.1 h5; omega)
    apply WindowLocalAssembly.reward_lift_deadline x _ (B*n*(span x i+1)) T _ hlocal'
    unfold T
    calc
      _ ≤ (B*n)*(2*L) := Nat.mul_le_mul_left _ (by have := cut.2.1; omega)
      _ = _ := by ac_rfl
  · have hD : D≤n := by
      exact Nat.max_le.mpr ⟨by omega, Nat.le_trans (Nat.min_le_left _ _) hnL⟩
    have h6 : 6≤H := (Nat.le_div_iff_mul_le cut.1).mpr (Nat.mul_le_mul_left 6 hD)
    refine ⟨{ k := rank x
              roster := WindowRoster.roster x
              inj := WindowRoster.roster_injective x
              starts := []
              nodup := List.nodup_nil
              many := by simp only [List.length_nil,Nat.zero_add]; omega
              trial := ?_ }⟩
    intro i hi
    cases hi

theorem rooted_mean {p n : Nat} (x : Config p 12 n) (hp : 2≤p) (hn : 4≤n) (hN : n≤boundedN)
    (root : RootedEntrance.RootNonempty x) :
    IIDExpectedHittingTimeAtMost step SafeOneLeader x (coefficient*n^2) := by
  have retire (y : Config p 12 n) (hy : QuietEntrance y) (hr : 2≤rank y) :
      IIDExpectedHittingTimeAtMost step (fun z => rank z < rank y) y (retirement*n^2) :=
    WindowCappedRetirement.bounded_at 12 (by decide) y hp hn hy hr
  have hw : 0<window := by decide
  let s : Stage step x :=
    ⟨Config p 12 n,x,step,id,QuietEntrance,fun _ => True,rfl,fun _ _ => rfl,trivial,fun _ _ _ => trivial⟩
  have hh := expected_with_preparation s SafeOneLeader (2049*n^2) (patrol*n^2)
    (rooted_rear_entrance_printed x hp (by decide) hn root) (by
      intro y _ hy _
      have tail := rooted_tail_of_windows y hn
        (fun z e h => RootedFresh.quiet_step z e hp (by decide) hn h) hy
        retirement (2*window) 60 (17+64*(2*12+1)) (by omega) (by decide)
        (fun z hz hr => retire z hz hr)
        (by
          intro L hL hLn
          obtain ⟨H,hHL,h⟩ := marginal n L hn hN hL hLn
          exact ⟨H,hHL,fun z hz => h z hp hz⟩)
        (fun z hz hr => RootedSingleton.singletonSafeMean z hp (by decide) hn hz hr)
      have eq : 8*(32*(2*window))+8*60*retirement+(17+64*(2*12+1))=patrol := by
        unfold patrol; omega
      rw [eq] at tail
      exact tail)
  simpa only [coefficient,Nat.add_mul] using hh

theorem bounded_suffix_at_coefficient {n : Nat} (hn : 4≤n) (hN : n≤boundedN)
    (x : BoundedRaw n) :
    Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (coefficient*n^2) := by
  have hp : 2 ≤ boundedP := by decide
  have hnPos : 0 < n := by omega
  have hs : n < boundedP := Nat.lt_succ_of_le hN
  have hnd : ¬ boundedP ∣ n :=
    fun hd => Nat.not_le_of_lt hs (Nat.le_of_dvd hnPos hd)
  have hroot := RootedAssembly.rootNonempty_of_not_dvd (boundedProject x) hn hnd
  apply (MonitorRawBridge.height_iff_row _ _ _ _).2
  exact RootedProduct.public_mean_to_product boundedNext boundedProject boundedLeader
    (fun _ => True) (fun _ _ _ => trivial)
    (fun y e _ => BoundedPublicCodec.bounded_projects y e) (fun _ _ _ => rfl)
    x trivial _ (rooted_mean (boundedProject x) hp hn hN hroot)

end L4.WindowCappedPublic
