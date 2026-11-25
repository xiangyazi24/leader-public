import Leader.L4.WindowCappedClocks
import Leader.L4.WindowCappedLinearEntry

namespace L4.WindowCappedMean
open WindowCappedPlan WindowCappedMiddle WindowPlan WindowTransactions
open WindowFiveStages WindowA0Join WindowClock TripleRenewal
open SevenTagCharge WindowRoster RootedAssembly RankRenewal WindowLatch

theorem physical_cap {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (w : Word n) : physical x i w+1≤n :=
  Nat.succ_le_of_lt (WindowSpanEndpoints.width_lt
    (WindowSpanTrace.selected x i w).l (WindowSpanTrace.selected x i w).r)

variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))

theorem normalize_allow (j : Nat) (hj : j≤4) (w : Word n) (h : Nat)
    (H : Allow hp hc hn x hq i j w h) :
    Allow hp hc hn x hq i j w (min h (n-1)) := by
  have J : j=0∨j=1∨j=2∨j=3∨j=4 := by omega
  have K : physical x i w≤n-1 := by have := physical_cap x i w; omega
  rcases J with rfl|rfl|rfl|rfl|rfl
  · exact H
  all_goals
    simp only [Allow] at H ⊢
    rcases H with H|⟨A,B⟩
    · exact .inl H
    · exact .inr ⟨Nat.le_min.mpr ⟨A,K⟩,B⟩

theorem transaction_prep {C h : Nat} {w : Word n} (K : Transaction C w h) :
    IIDExpectedHittingTimeAtMost (suffixStage w K.hit).next
      (suffixStage w K.hit).ready (suffixStage w K.hit).start (C*n*(h+1)) := by
  intro t
  change iidHitCost wordNext (FirstExit K.hit) t [] ≤ _
  rw [cost_firstExit K.hit t [] (clean_nil _)]
  exact K.mean t

theorem sharp_slot (h7 : 7≤RankPhysical.rank x) (j : Nat) (hj : j<4) :
    SharpSlot hp hc hn x hq i j := by
  have J : j=0∨j=1∨j=2∨j=3 := by omega
  rcases J with rfl|rfl|rfl|rfl
  · exact WindowCappedPlan.protected_slot hp hc hn x hq i h7
  · exact WindowCappedMiddle.triple_slot hp hc hn x hq i h7
  · exact WindowCappedMiddle.pair_slot hp hc hn x hq i h7
  · exact WindowCappedMiddle.singleton_slot hp hc hn x hq i h7

theorem last_four (h7 : 7≤RankPhysical.rank x) (N : Nat) (hN : n≤N)
    (j : Nat) (hj : j≤4) (w : Word n) (h : Nat)
    (A : Allow hp hc hn x hq i j w h) (hh : h+1≤n) :
    IIDExpectedHittingTimeAtMost wordNext (done hp hc hn x hq i) w
      (j*(4096*n*N)) := by
  induction j generalizing w h with
  | zero =>
    intro t
    change done hp hc hn x hq i w at A
    rw [iidHitCost_of_target _ _ _ A]
    exact Nat.zero_le _
  | succ j ih =>
    by_cases B : done hp hc hn x hq i w
    · intro t
      rw [iidHitCost_of_target _ _ _ B]
      exact Nat.zero_le _
    obtain skip|⟨T,H⟩ := sharp_slot hp hc hn x hq i h7 j (by omega) w h A B
    · exact expected_mono (ih (by omega) w h skip hh)
        (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · have prep := expected_mono (transaction_prep T)
        (Nat.mul_le_mul_left (4096*n) (Nat.le_trans hh hN))
      have ht := expected_with_preparation (suffixStage w T.hit)
        (done hp hc hn x hq i) (4096*n*N) (j*(4096*n*N)) prep (by
          intro u _ hu nd
          change Word n at u
          have A' := normalize_allow hp hc hn x hq i j (by omega) (w++u) _
            (H u hu nd)
          have cap := Nat.min_le_right (T.span u) (n-1)
          exact ih (by omega) (w++u) _ A' (by omega))
      rw [show (j+1)*(4096*n*N)=4096*n*N+j*(4096*n*N) by
        rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]]
      exact ht

def windowCoeff (c N : Nat) : Nat := 4*((WindowCappedLinearEntry.entryK c N) + 4*4096*N)

theorem initial_mean (h7 : 7≤RankPhysical.rank x) (N : Nat) (hN : n≤N)
    (short : 2*WindowSpan.span x i+2<n) :
    IIDExpectedHittingTimeAtMost wordNext (done hp hc hn x hq i) []
      (((WindowCappedLinearEntry.entryK c N) + 4*4096*N)*n*(WindowSpan.span x i+1)) := by
  let h := WindowSpan.span x i
  have B : (WindowCappedLinearEntry.entryK c N)*n*(h+1) + 4*(4096*n*N) ≤
      ((WindowCappedLinearEntry.entryK c N)+4*4096*N)*n*(h+1) := by
    rw [Nat.add_mul,Nat.add_mul]
    apply Nat.add_le_add_left
    calc
      _ = (4*4096*N)*n := by ac_rfl
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  by_cases D : done hp hc hn x hq i []
  · intro t
    rw [iidHitCost_of_target _ _ _ D]
    exact Nat.zero_le _
  have h5 : 5≤n := by have := RankBlockContraction.rank_le_size x; omega
  obtain skip|⟨T,H⟩ := WindowCappedLinearEntry.entry_slot hp hc hn x hq i N hN h5 h7 short [] h ⟨rfl,rfl⟩ D
  · have H := normalize_allow hp hc hn x hq i 4 (by decide) [] h skip
    have cap := Nat.min_le_right h (n-1)
    apply expected_mono (last_four hp hc hn x hq i h7 N hN 4 (by decide) [] _ H (by omega))
    exact Nat.le_trans (Nat.le_add_left _ _) B
  · apply expected_mono (B := (((WindowCappedLinearEntry.entryK c N)+4*4096*N)*n*(h+1))) _ B
    apply expected_with_preparation (suffixStage [] T.hit) _ _ _ (transaction_prep T)
    intro u _ hu nd
    change Word n at u
    have H' := normalize_allow hp hc hn x hq i 4 (by decide) ([]++u) _
      (H u hu nd)
    have cap := Nat.min_le_right (T.span u) (n-1)
    exact last_four hp hc hn x hq i h7 N hN 4 (by decide) ([]++u) _ H' (by omega)

include hp hc hn hq in
theorem capped_reward (h7 : 7≤RankPhysical.rank x) (N : Nat) (hN : n≤N)
    (short : 2*WindowSpan.span x i+2<n) :
    let T := windowCoeff c N*n*(WindowSpan.span x i+1)
    12*n^T ≤ 25*endpointSum wordNext (reward x (window7 (roster x) i)) T [] := by
  let T := windowCoeff c N*n*(WindowSpan.span x i+1)
  let K := ((WindowCappedLinearEntry.entryK c N)+4*4096*N)*n*(WindowSpan.span x i+1)
  have C : 0<(WindowCappedLinearEntry.entryK c N) := by unfold WindowCappedLinearEntry.entryK; omega
  have hK : 0<K := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hT : 4*K≤T := by
    change 4*(((WindowCappedLinearEntry.entryK c N)+4*4096*N)*n*(WindowSpan.span x i+1)) ≤
      4*((WindowCappedLinearEntry.entryK c N)+4*4096*N)*n*(WindowSpan.span x i+1)
    exact Nat.le_of_eq (by ac_rfl)
  have H := window_reward_of_budget wordNext (done hp hc hn x hq i)
    (LedgerReward x (window7 (roster x) i)) (fun _ => False) (freshBad hp hc hn x hq i)
    (WindowFrontDone.fold_closed hp hc hn hq (scope x i))
    (fun w h _ nb => WindowFrontDone.fold_cover hp hc hn hq (scope x i) w h nb)
    K T hK hT [] (initial_mean hp hc hn x hq i h7 N hN short)
    (by rw [no_entry_mass,Nat.mul_zero]; exact Nat.zero_le _)
    (WindowOwnership.fold_fresh_mass hp hc hn hq (scope x i) T)
  have hr : indicator (LedgerReward x (window7 (roster x) i)) = reward x (window7 (roster x) i) :=
    funext (ledgerReward_indicator x _)
  rwa [hr] at H

#print axioms physical_cap
#print axioms capped_reward

end L4.WindowCappedMean
