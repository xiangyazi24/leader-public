import Leader.L4.FourLossStickyClock
import Leader.L4.ReportHalfCellClock
import Leader.L4.ReportLossArithmetic
import Leader.L4.MonitorRawBridge
import Leader.L4.PhysicalCustody

namespace L4.ReportFourLossBridge
open AllSizeProtocol PhysicalCustody FourLossStickyClock
open AdviceBandRadiusBudget ReportLossArithmetic

section HalfCell
variable {X J : Type} {n : Nat}

theorem publication_halfcell_tail [DecidableEq J] (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    {h H mu : Nat} (N : 0<n) (HH : 0<H) (Mu : 0<mu)
    (mean : ShortTwoPublicationClock.UniformPublicationMean step classify Good (mu*n))
    (who : J) (x : X) (G : Good x) :
    2^(h/(80*H*mu)) *
      badCount (fun w=>who∉ShortNORCover.publications step classify x w) (halfCell n h H)
      ≤ n^(halfCell n h H) := by
  have A : 0<mu*n := Nat.mul_pos Mu N
  have B : 0<2*(mu*n) := Nat.mul_pos (by decide) A
  apply ReportHalfCellClock.target_publication_tail step classify Good closed (mu*n) A
    mean who x G
  apply (Nat.le_div_iff_mul_le B).mp
  simpa only [Nat.mul_assoc] using (halfcell_attempts (h:=h) N HH Mu)

end HalfCell

/-- A post-epoch interface on the actual immutable physical scheduler.
It assumes the true four block counts and deterministic trial soundness,
not Cover reachability or a global hitting-time conclusion. -/
structure Trial {s n : Nat} (rho : Nat)
    (Good : Raw s n→Prop) (Sticky : Fin n→Raw s n→Prop) where
  loss : Fin n → Raw s n → Fin 4 → List (Fin n)→Prop
  closed : ∀ x e,Good x→Good (rawNext s x e)
  sticky : ∀ i x e,Good x→Sticky i x→Sticky i (rawNext s x e)
  sound : ∀ i x,Good x→¬Sticky i x→
    ∀ w,w.length=n*trialU rho→¬Sticky i (Height.runWord (rawNext s) x w)→
      ∃ j,loss i x j w
  cap : ∀ i x,Good x→¬Sticky i x→∀ j,
    8*badCount (loss i x j) (n*trialU rho)≤n^(n*trialU rho)

theorem raw_report_mean {s n rho : Nat} (N : 0<n)
    (Good : Raw s n→Prop) (Sticky : Fin n→Raw s n→Prop)
    (I : Trial rho Good Sticky) (x : Raw s n) (G : Good x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (Cover Good Sticky)
      x (2*n*trialU rho*(ell n+1)) := by
  have T := cover_expected_of_four (rawNext s) Good Sticky
    (n*trialU rho) N I.loss I.closed I.sticky I.sound I.cap x G
  exact (MonitorRawBridge.height_iff_row _ _ _ _).mp
    (show Height.IIDExpectedHittingTimeAtMost (rawNext s) (Cover Good Sticky)
      x (2*n*trialU rho*(ell n+1)) from by
      have E : 2*(ell n+1)*(n*trialU rho)=2*n*trialU rho*(ell n+1) := by ac_rfl
      rwa [E] at T)

end L4.ReportFourLossBridge
