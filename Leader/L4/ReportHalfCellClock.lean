import Leader.L4.FourLossStickyClock
import Leader.L4.ShortTwoPublicationClock

namespace L4.ReportHalfCellClock
open Height Classical FourLossStickyClock

variable {X J : Type} {n : Nat}

theorem nohit_pad (step : X→Fin n→X) (hit : X→Prop)
    (keep : ∀ x e,hit x→hit (step x e)) (x : X) (a b : Nat) :
    badCount (fun w=>¬hit (runWord step x w)) (a+b) ≤
      n^b*badCount (fun w=>¬hit (runWord step x w)) a := by
  unfold badCount
  rw [wordSum_add,←wordSum_mul_left]
  apply wordSum_mono
  intro u
  dsimp only
  by_cases H : hit (runWord step x u)
  · simp only [H,not_true_eq_false,if_false,Nat.mul_zero]
    have Z : ∀ v, hit (runWord step x (u++v)) := by
      intro v
      rw [runWord_append]
      exact runWord_of_closed step hit keep _ _ H
    rw [wordSum_congr_fun _ (fun _=>0) _ (fun v=>by simp [Z v]),wordSum_const_zero]
    exact Nat.le_refl _
  · simp only [H,not_false_eq_true,if_true,Nat.mul_one]
    rw [←wordSum_const_one (n:=n) b]
    apply wordSum_mono
    intro w
    split <;> omega

/-- From a uniform mean A, every complete interval of length 2A
has half-event failure; partial padding stays on the original tape. -/
theorem tail_from_uniform_mean (step : X→Fin n→X) (Good hit : X→Prop)
    (good_closed : ∀ x e,Good x→Good (step x e))
    (keep : ∀ x e,hit x→hit (step x e))
    (A : Nat) (apos : 0<A)
    (mean : ∀ x,Good x→Height.IIDExpectedHittingTimeAtMost step hit x A)
    (x : X) (G : Good x) (b j : Nat) (fits : j*(2*A)≤b) :
    2^j*badCount (fun w=>¬hit (runWord step x w)) b ≤ n^b := by
  have same (y : X) (a : Nat) :
      wordSum (fun w=>if hit (runWord step y w) then 0 else 1) a=
        badCount (fun w=>¬hit (runWord step y w)) a := by
    unfold badCount
    apply wordSum_congr_fun
    intro w
    by_cases H : hit (runWord step y w) <;> simp [H]
  have F (y : X) (Y : Good y) : 2*wordSum
      (fun w=>if hit (runWord step y w) then 0 else 1) (2*A) ≤ n^(2*A) := by
    have M := markov_survivors step hit y A (2*A) (mean y Y)
    have E : wordSum (fun w=>if hit (stoppedRun step hit y w) then 0 else 1) (2*A)=
        wordSum (fun w=>if hit (runWord step y w) then 0 else 1) (2*A) := by
      apply wordSum_congr_fun
      intro w
      have R := stoppedRun_mem_iff_runWord_mem step hit keep y w
      by_cases H : hit (runWord step y w)
      · simp [H,R.mpr H]
      · have K : ¬hit (stoppedRun step hit y w) := fun t=>H (R.mp t)
        simp [H,K]
    rw [E] at M
    have T := Nat.le_of_mul_le_mul_left (show A*(2*wordSum
        (fun w=>if hit (runWord step y w) then 0 else 1) (2*A))≤A*(n^(2*A)) from by
      simpa only [←Nat.mul_assoc,Nat.mul_comm A 2] using M) apos
    exact T
  have V := restart_tail (D:=2*A) step hit Good keep good_closed (fun y Y _=>F y Y) x G j
  rw [same] at V
  obtain ⟨k,K⟩ := Nat.exists_eq_add_of_le fits
  rw [K,Nat.pow_add]
  calc
    _ ≤ 2^j*(n^k*badCount (fun w=>¬hit (runWord step x w)) (j*(2*A))) :=
      Nat.mul_le_mul_left _ (nohit_pad step hit keep x (j*(2*A)) k)
    _ = n^k*(2^j*badCount (fun w=>¬hit (runWord step x w)) (j*(2*A))) := by ac_rfl
    _ ≤ n^k*n^(j*(2*A)) := Nat.mul_le_mul_left _ V
    _ = _ := Nat.mul_comm _ _

/-- Classification always uses the old raw mark, and the monitor
always executes the real transition even when the flag is already set. -/
theorem target_publication_tail [DecidableEq J] (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (A : Nat) (apos : 0<A)
    (mean : ShortTwoPublicationClock.UniformPublicationMean step classify Good A)
    (who : J) (x : X) (G : Good x) (b j : Nat) (fits : j*(2*A)≤b) :
    2^j*badCount (fun w=>who∉ShortNORCover.publications step classify x w) b ≤ n^b := by
  let next := ShortTwoPublicationClock.phase step classify who
  let hit := ShortTwoPublicationClock.goal (X:=X) who
  let gd := fun p : X×Bool=>Good p.1
  have C (y : X×Bool) (e : Fin n) (Y : gd y) : gd (next y e) := closed _ _ Y
  have K (y : X×Bool) (e : Fin n) (Y : hit y) : hit (next y e) := by
    change y.2=true at Y
    simp [next,hit,ShortTwoPublicationClock.phase,ShortTwoPublicationClock.goal,Y]
  have M (y : X×Bool) (Y : gd y) : Height.IIDExpectedHittingTimeAtMost next hit y A := by
    rcases y with ⟨y,f⟩
    cases f
    · exact mean who y Y
    · intro t
      rw [Height.iidHitCost_of_target next hit (y,true) (show hit (y,true) from rfl)]
      exact Nat.zero_le _
  have V := tail_from_uniform_mean next gd hit C K A apos M (x,false) G b j fits
  have E : badCount (fun w=>who∉ShortNORCover.publications step classify x w) b =
      badCount (fun w=>¬hit (runWord next (x,false) w)) b := by
    unfold badCount
    apply wordSum_congr_fun
    intro w
    have eq (v : List (Fin n)) (z : X×Bool) :
        runWord next z v=SequentialMarkClock.run next z v := by
      induction v generalizing z with
      | nil => rfl
      | cons e v ih => exact ih (next z e)
    have H := ShortTwoPublicationClock.flag_eq step classify who (x,false) w
    change hit (SequentialMarkClock.run next (x,false) w) ↔ _ at H
    simp only [Bool.false_eq_true,false_or] at H
    have F : hit (runWord next (x,false) w) ↔ who∈ShortNORCover.publications step classify x w := by
      rw [eq]
      exact H
    by_cases U : who∈ShortNORCover.publications step classify x w
    · simp [U,F.mpr U]
    · have W : ¬hit (runWord next (x,false) w) := fun a=>U (F.mp a)
      simp [U,W]
  rwa [E]

end L4.ReportHalfCellClock
