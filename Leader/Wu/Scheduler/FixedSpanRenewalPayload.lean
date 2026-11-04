import Leader.Core.FiniteUniformStoppingTree
import Leader.Wu.Elimination.SpanChargedOnce
import Leader.Wu.RaceEntrance.ArrivalRaceMass
import Leader.Wu.Scheduler.Probability
import Leader.Core.EpisodeTelescope

/-!
# Payload-preserving finite-word renewal

This module integrates the candidate against the repository's real
stopping-tree, site-credit, episode-telescope, and K2 interfaces. The generic
renewal proof is restricted to a closed retry carrier. The physical adapter
uses actual reachability from one fixed start and actual first-success
post-states. Uniform entrance mass and the original span-credit producer are
not supplied here. The fixed-horizon cost row is proved directly by counting
all active raw interactions, including unfinished service prefixes.
-/

set_option autoImplicit false

namespace FixedSpanRenewalPayload

open FiniteUniformStoppingTree
open NonrenewableCredits

/-!
A macro scheduler symbol represents one fixed-length physical scheduler word.
The successful constructor retains the actual physical successor.  Its erasure
below is the real payloadless `FiniteUniformStoppingTree.StopNode.success`.
-/
/-- A macro block either succeeds with its actual endpoint, or retries with its actual residual state. -/
inductive PayloadOutcome (S : Type) where
  | success : S → PayloadOutcome S
  | retry : S → PayloadOutcome S
  deriving DecidableEq


/-- Forget only the successful payload, mapping retries to the existing active constructor. -/
def erasePayload {S : Type} : PayloadOutcome S → StopNode S
  | .success _ => .success
  | .retry x => .active x


/-- The existing stopped-tree transition associated with a payload-preserving block. -/
def macroStep {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) :
    S → Fin M → StopNode S :=
  fun x e => erasePayload (outcome x e)


/-- Unit weight for a successful payload. -/
def successBit {S : Type} : PayloadOutcome S → Nat
  | .success _ => 1
  | .retry _ => 0


/-- Unit weight for an unfinished payload. -/
def retryBit {S : Type} : PayloadOutcome S → Nat
  | .success _ => 0
  | .retry _ => 1


/-- The exact endpoint credit on successful words, zero on retries. -/
def terminalWordCredit {S : Type} (terminalCredit : S → Nat) :
    PayloadOutcome S → Nat
  | .success y => terminalCredit y
  | .retry _ => 0


/-- The same original episode credit on each retry, zero on successes. -/
def retryWordCredit {S : Type} (episodeCredit : Nat) :
    PayloadOutcome S → Nat
  | .success _ => 0
  | .retry _ => episodeCredit


/-- Unnormalized count of successful macro symbols. -/
def successMass {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) : Nat :=
  (List.ofFn (fun e => successBit (outcome x e))).sum


/-- Unnormalized count of active retry symbols. -/
def retryMass {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) : Nat :=
  (List.ofFn (fun e => retryBit (outcome x e))).sum


/-- Sum of actual block costs over the complete finite macro alphabet. -/
def blockCostMass {S : Type} {M : Nat}
    (wordCost : S → Fin M → Nat) (x : S) : Nat :=
  (List.ofFn (fun e => wordCost x e)).sum


/-- Sum of the successor-dependent residual credits over successful symbols. -/
def terminalCreditMass {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (terminalCredit : S → Nat) (x : S) : Nat :=
  (List.ofFn (fun e =>
    terminalWordCredit terminalCredit (outcome x e))).sum


/-- Sum of the unchanged original episode credit over retry symbols. -/
def retryCreditMass {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (episodeCredit : Nat) (x : S) : Nat :=
  (List.ofFn (fun e =>
    retryWordCredit episodeCredit (outcome x e))).sum


/-- Successful payload counts agree with the real one-step stopped-tree count. -/
theorem successMass_eq_successCount
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) :
    successMass outcome x =
      successCount (macroStep outcome) (.active x) 1 := by
  unfold successMass successCount macroStep
  simp only [treeWeight, stepNode]
  apply ofFn_sum_eq
  intro e
  cases outcome x e <;> rfl


/-- Retry payload counts agree with the real one-step active count. -/
theorem retryMass_eq_activeCount
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) :
    retryMass outcome x =
      activeCount (macroStep outcome) (.active x) 1 := by
  unfold retryMass activeCount macroStep
  simp only [treeWeight, stepNode]
  apply ofFn_sum_eq
  intro e
  cases outcome x e <;> rfl


private theorem macro_failureCount_eq_zero
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) :
    failureCount (macroStep outcome) (.active x) 1 = 0 := by
  unfold failureCount macroStep
  simp only [treeWeight, stepNode]
  calc
    (List.ofFn (fun e : Fin M =>
        failureWeight (erasePayload (outcome x e)))).sum =
        (List.ofFn (fun _ : Fin M => 0)).sum := by
      apply ofFn_sum_eq
      intro e
      cases outcome x e <;> rfl
    _ = M * 0 := ofFn_sum_const M 0
    _ = 0 := Nat.mul_zero M


/-- The requested `S+F=M` is not assumed after payload preservation: it is
obtained from the retained stopped-tree partition.  The erasure has no failure
branch, so every macro word is either a retained success or an active retry. -/
theorem mass_partition_from_stopped_tree
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) :
    successMass outcome x + retryMass outcome x = M := by
  have hp :=
    node_count_partition (macroStep outcome) (.active x) 1
  have ha := retryMass_eq_activeCount outcome x
  have hs := successMass_eq_successCount outcome x
  have hf := macro_failureCount_eq_zero outcome x
  rw [← ha, ← hs, hf] at hp
  simpa [Nat.pow_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hp


private theorem retry_mass_le_of_rows
    {M Q S F : Nat}
    (hQ : 0 < Q)
    (hmass : M ≤ Q * S)
    (hpartition : S + F = M) :
    F ≤ (Q - 1) * S := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hQ)
  subst Q
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Nat.add_mul, Nat.one_mul] at hmass ⊢
  omega


private theorem blockCost_le_exact_success_budget
    {M Q S F base extra C : Nat}
    (hQ : 0 < Q)
    (hmass : M ≤ Q * S)
    (hpartition : S + F = M)
    (hcost : C ≤ M * base + F * extra) :
    C ≤ S * (Q * base + (Q - 1) * extra) := by
  have hF := retry_mass_le_of_rows hQ hmass hpartition
  have hb : M * base ≤ (Q * S) * base :=
    Nat.mul_le_mul_right base hmass
  have he : F * extra ≤ ((Q - 1) * S) * extra :=
    Nat.mul_le_mul_right extra hF
  calc
    C ≤ M * base + F * extra := hcost
    _ ≤ (Q * S) * base + ((Q - 1) * S) * extra :=
      Nat.add_le_add hb he
    _ = S * (Q * base + (Q - 1) * extra) := by
      rw [Nat.mul_add]
      ac_rfl


private theorem successCreditMass_le
    {S : Type} {M budget episodeCredit : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (terminalCredit : S → Nat) (x : S)
    (hsuccess : ∀ e y, outcome x e = .success y →
      budget + terminalCredit y ≤ episodeCredit) :
    successMass outcome x * budget +
        terminalCreditMass outcome terminalCredit x ≤
      successMass outcome x * episodeCredit := by
  have hsum :=
    ofFn_sum_le
      (fun e : Fin M =>
        budget * successBit (outcome x e) +
          terminalWordCredit terminalCredit (outcome x e))
      (fun e : Fin M =>
        episodeCredit * successBit (outcome x e))
      (by
        intro e
        cases ho : outcome x e with
        | success y =>
            simpa [successBit, terminalWordCredit, ho] using
              hsuccess e y ho
        | retry r =>
            simp [successBit, terminalWordCredit])
  simpa only [successMass, terminalCreditMass,
    ofFn_sum_add, ofFn_sum_mul_left, Nat.mul_comm] using hsum


/-- Every unfinished word retains the identical original-start credit. -/
theorem retryCreditMass_eq
    {S : Type} {M episodeCredit : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (x : S) :
    retryCreditMass outcome episodeCredit x =
      retryMass outcome x * episodeCredit := by
  calc
    retryCreditMass outcome episodeCredit x =
        (List.ofFn (fun e : Fin M =>
          episodeCredit * retryBit (outcome x e))).sum := by
      unfold retryCreditMass
      apply ofFn_sum_eq
      intro e
      cases outcome x e <;> simp [retryWordCredit, retryBit]
    _ = episodeCredit *
        (List.ofFn (fun e : Fin M => retryBit (outcome x e))).sum :=
      ofFn_sum_mul_left episodeCredit _
    _ = retryMass outcome x * episodeCredit := by
      unfold retryMass
      rw [Nat.mul_comm]


private theorem local_payload_residual_row
    {S : Type} {M Q base extra budget episodeCredit : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (x : S)
    (hQ : 0 < Q)
    (hmass : M ≤ Q * successMass outcome x)
    (hcost : blockCostMass wordCost x ≤
      M * base + retryMass outcome x * extra)
    (hpartition : successMass outcome x + retryMass outcome x = M)
    (hbudget : Q * base + (Q - 1) * extra ≤ budget)
    (hsuccess : ∀ e y, outcome x e = .success y →
      budget + terminalCredit y ≤ episodeCredit) :
    blockCostMass wordCost x +
        terminalCreditMass outcome terminalCredit x +
        retryCreditMass outcome episodeCredit x ≤
      M * episodeCredit := by
  have hExact :
      blockCostMass wordCost x ≤
        successMass outcome x *
          (Q * base + (Q - 1) * extra) :=
    blockCost_le_exact_success_budget
      hQ hmass hpartition hcost
  have hCostBudget :
      blockCostMass wordCost x ≤
        successMass outcome x * budget :=
    Nat.le_trans hExact
      (Nat.mul_le_mul_left (successMass outcome x) hbudget)
  have hSuccess :=
    successCreditMass_le outcome terminalCredit x hsuccess
  have hRetry :=
    retryCreditMass_eq (episodeCredit := episodeCredit) outcome x
  calc
    blockCostMass wordCost x +
          terminalCreditMass outcome terminalCredit x +
          retryCreditMass outcome episodeCredit x ≤
        (successMass outcome x * budget +
          terminalCreditMass outcome terminalCredit x) +
          retryCreditMass outcome episodeCredit x :=
      Nat.add_le_add_right
        (Nat.add_le_add_right hCostBudget _) _
    _ ≤ successMass outcome x * episodeCredit +
          retryCreditMass outcome episodeCredit x :=
      Nat.add_le_add_right hSuccess _
    _ = successMass outcome x * episodeCredit +
          retryMass outcome x * episodeCredit := by
      rw [hRetry]
    _ = (successMass outcome x + retryMass outcome x) *
          episodeCredit := by
      rw [Nat.add_mul]
    _ = M * episodeCredit := by
      rw [hpartition]


/-- Physical block cost plus successful endpoint credit or original retry credit. -/
def rowWordResidual
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (episodeCredit : Nat)
    (x : S) (e : Fin M) : Nat :=
  wordCost x e + terminalWordCredit terminalCredit (outcome x e) +
    retryWordCredit episodeCredit (outcome x e)


private theorem rowWordResidual_sum
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (episodeCredit : Nat)
    (x : S) :
    (List.ofFn (fun e : Fin M =>
      rowWordResidual outcome wordCost terminalCredit episodeCredit x e)).sum =
      blockCostMass wordCost x +
        terminalCreditMass outcome terminalCredit x +
        retryCreditMass outcome episodeCredit x := by
  unfold rowWordResidual blockCostMass terminalCreditMass retryCreditMass
  calc
    (List.ofFn (fun e : Fin M =>
        (wordCost x e +
          terminalWordCredit terminalCredit (outcome x e)) +
          retryWordCredit episodeCredit (outcome x e))).sum =
        (List.ofFn (fun e : Fin M =>
          wordCost x e +
            terminalWordCredit terminalCredit (outcome x e))).sum +
        (List.ofFn (fun e : Fin M =>
          retryWordCredit episodeCredit (outcome x e))).sum :=
      ofFn_sum_add _ _
    _ =
        ((List.ofFn (fun e : Fin M => wordCost x e)).sum +
          (List.ofFn (fun e : Fin M =>
            terminalWordCredit terminalCredit (outcome x e))).sum) +
        (List.ofFn (fun e : Fin M =>
          retryWordCredit episodeCredit (outcome x e))).sum := by
      rw [ofFn_sum_add]


/-!
`T=0` retains the full original episode credit at an active frontier.
At `T+1`, first-block physical cost is repeated over all `M^T` suffix words.
A success is padded by its actual terminal credit; a retry continues from its
actual residual state.  Thus no block boundary resets state, cost, or credit.
-/
/-- Exact finite-depth renewal numerator, retaining the active original-start credit at depth zero. -/
def renewalResidualNumerator
    {S : Type} {M : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (episodeCredit : Nat) :
    S → Nat → Nat
  | _, 0 => episodeCredit
  | x, T + 1 =>
      (List.ofFn (fun e : Fin M =>
        M ^ T * wordCost x e +
          match outcome x e with
          | .success y => M ^ T * terminalCredit y
          | .retry r =>
              renewalResidualNumerator outcome wordCost
                terminalCredit episodeCredit r T)).sum


/-- Exact finite-word renewal residual.

The row hypotheses are stated using the retained stopped-tree counts of the
payload-erased macro step.  `S+F=M` is obtained from
`FiniteUniformStoppingTree.node_count_partition`, because `macroStep` has no
failure branch.  The successful successor itself is retained only by
`PayloadOutcome.success y` so its terminal credit can be inserted.

There is no bound on the number of retries. -/
theorem renewalResidualNumerator_le_on
    {S : Type} {M Q base extra budget : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (episodeCredit : Nat)
    (Allowed : S → Prop)
    (hclosed : ∀ x, Allowed x → ∀ e r, outcome x e = .retry r → Allowed r)
    (hQ : 0 < Q)
    (hmass : ∀ x, Allowed x →
      M ≤ Q * successCount (macroStep outcome) (.active x) 1)
    (hcost : ∀ x, Allowed x →
      blockCostMass wordCost x ≤
        M * base +
          activeCount (macroStep outcome) (.active x) 1 * extra)
    (hbudget : Q * base + (Q - 1) * extra ≤ budget)
    (hsuccess : ∀ x, Allowed x → ∀ e y, outcome x e = .success y →
      budget + terminalCredit y ≤ episodeCredit) :
    ∀ x, Allowed x → ∀ T,
      renewalResidualNumerator outcome wordCost
          terminalCredit episodeCredit x T ≤
        M ^ T * episodeCredit := by
  intro x hx T
  induction T generalizing x with
  | zero =>
      simp [renewalResidualNumerator]
  | succ T ih =>
      have hm : M ≤ Q * successMass outcome x := by
        calc
          M ≤ Q * successCount (macroStep outcome) (.active x) 1 :=
            hmass x hx
          _ = Q * successMass outcome x := by
            rw [successMass_eq_successCount outcome x]
      have hc :
          blockCostMass wordCost x ≤
            M * base + retryMass outcome x * extra := by
        calc
          blockCostMass wordCost x ≤
              M * base +
                activeCount (macroStep outcome) (.active x) 1 * extra :=
            hcost x hx
          _ = M * base + retryMass outcome x * extra := by
            rw [retryMass_eq_activeCount outcome x]
      have hp := mass_partition_from_stopped_tree outcome x
      have hlocal :=
        local_payload_residual_row
          outcome wordCost terminalCredit x
          hQ hm hc hp hbudget (hsuccess x hx)
      have hpoint : ∀ e : Fin M,
          M ^ T * wordCost x e +
              (match outcome x e with
              | .success y => M ^ T * terminalCredit y
              | .retry r =>
                  renewalResidualNumerator outcome wordCost
                    terminalCredit episodeCredit r T) ≤
            M ^ T *
              rowWordResidual outcome wordCost terminalCredit
                episodeCredit x e := by
        intro e
        cases ho : outcome x e with
        | success y =>
            simp only [ho, rowWordResidual, terminalWordCredit,
              retryWordCredit, Nat.add_zero]
            simp only [Nat.mul_add]
            exact Nat.le_refl _
        | retry r =>
            have hir := ih r (hclosed x hx e r ho)
            simp only [ho, rowWordResidual, terminalWordCredit,
              retryWordCredit, Nat.add_zero]
            calc
              M ^ T * wordCost x e +
                    renewalResidualNumerator outcome wordCost
                      terminalCredit episodeCredit r T ≤
                  M ^ T * wordCost x e + M ^ T * episodeCredit :=
                Nat.add_le_add_left hir _
              _ = M ^ T * (wordCost x e + episodeCredit) := by
                rw [Nat.mul_add]
      change
        (List.ofFn (fun e : Fin M =>
          M ^ T * wordCost x e +
            match outcome x e with
            | .success y => M ^ T * terminalCredit y
            | .retry r =>
                renewalResidualNumerator outcome wordCost
                  terminalCredit episodeCredit r T)).sum ≤
          M ^ (T + 1) * episodeCredit
      calc
        (List.ofFn (fun e : Fin M =>
          M ^ T * wordCost x e +
            match outcome x e with
            | .success y => M ^ T * terminalCredit y
            | .retry r =>
                renewalResidualNumerator outcome wordCost
                  terminalCredit episodeCredit r T)).sum ≤
            (List.ofFn (fun e : Fin M =>
              M ^ T * rowWordResidual outcome wordCost
                terminalCredit episodeCredit x e)).sum :=
          ofFn_sum_le _ _ hpoint
        _ = M ^ T *
            (List.ofFn (fun e : Fin M =>
              rowWordResidual outcome wordCost terminalCredit
                episodeCredit x e)).sum :=
          ofFn_sum_mul_left _ _
        _ = M ^ T *
            (blockCostMass wordCost x +
              terminalCreditMass outcome terminalCredit x +
              retryCreditMass outcome episodeCredit x) := by
          rw [rowWordResidual_sum]
        _ ≤ M ^ T * (M * episodeCredit) :=
          Nat.mul_le_mul_left _ hlocal
        _ = M ^ (T + 1) * episodeCredit := by
          rw [Nat.pow_succ]
          ac_rfl


/-! ## Project constants -/

/-- Base block budget, equal to an entrance horizon of `32*n*s` plus `4*n` race interactions. -/
def B0 (n s : Nat) : Nat :=
  n * (32 * s + 4)


/-- The stated retry-service allowance, kept separate from the base budget. -/
def D (n d : Nat) : Nat :=
  n * (4 * d + 1)


/-- Exact success-funded renewal tariff at denominator 32. -/
def K32 (n s d : Nat) : Nat :=
  32 * B0 n s + 31 * D n d


/-- The existing project episode tariff to be funded by nonrenewable span credit. -/
def E (n s : Nat) : Nat :=
  n * (2048 * s + 256)


/-- Global episode-telescope scale, exactly `2304*n`. -/
def EScale (n : Nat) : Nat :=
  2304 * n


/-- Exact arithmetic check for the accepted `32*B0 + 31*D` insight. -/
theorem K32_le_E {n s d : Nat} (hd : d ≤ s) :
    K32 n s d ≤ E n s := by
  have hinner :
      32 * (32 * s + 4) + 31 * (4 * d + 1) ≤
        2048 * s + 256 := by
    omega
  calc
    K32 n s d =
        n * (32 * (32 * s + 4) + 31 * (4 * d + 1)) := by
      unfold K32 B0 D
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ n * (2048 * s + 256) :=
      Nat.mul_le_mul_left n hinner
    _ = E n s := rfl


/-- A unit span charge funds the full episode tariff at scale `2304*n`. -/
theorem E_le_scale_of_span
    {n s drop : Nat} (hs : s ≤ drop + 1) :
    E n s ≤ EScale n * (drop + 1) := by
  have hinner :
      2048 * s + 256 ≤ 2304 * (drop + 1) := by
    omega
  calc
    E n s = n * (2048 * s + 256) := rfl
    _ ≤ n * (2304 * (drop + 1)) :=
      Nat.mul_le_mul_left n hinner
    _ = EScale n * (drop + 1) := by
      unfold EScale
      ac_rfl


/-- A successful macro word is funded from the ORIGINAL episode start.
Retries may have spent additional credits before `y`; no credit is reset.
The physical adapter below instantiates the phase with the actual leader count. -/
theorem original_span_funds_E
    {S : Type} {n s : Nat}
    (credits : S → Credits n) (leaders : S → Nat)
    (x0 y : S)
    (hspend : OnlySpends (credits x0) (credits y))
    (hspan : SpanChargedOnce 1 s (credits x0) (credits y))
    (hleader : leaders y < leaders x0) :
    E n s +
        EpisodeTelescope.amortizedPotential (EScale n)
          (fun z => w (credits z)) leaders y ≤
      EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) leaders x0 := by
  have hw : w (credits y) ≤ w (credits x0) :=
    spend_monotone (credits x0) (credits y) hspend
  have hs :
      s ≤ w (credits x0) - w (credits y) + 1 := by
    simpa only [SpanChargedOnce, Nat.one_mul] using hspan
  have hcost :
      E n s ≤
        EScale n *
          ((w (credits x0) - w (credits y)) + 1) :=
    E_le_scale_of_span hs
  exact EpisodeTelescope.one_episode_amortized
    (scale := EScale n)
    (w := fun z => w (credits z))
    (phase := leaders)
    (x := x0) (y := y) (c := E n s)
    hw hleader hcost


/-- Main project-facing substitution theorem.

`x0` is fixed for the entire elimination episode.  Every active macro-boundary
state `r` is required to satisfy the same physical mass and cost rows.  A
successful word must return the actual successor `y`; its span and leader drop
are measured from `x0`, not from `r`.

The conclusion holds at every finite retry horizon `T`; no deterministic retry
bound occurs anywhere. -/
theorem fixed_span_E_renewal_residual
    {S : Type} {M n s d : Nat}
    (outcome : S → Fin M → PayloadOutcome S)
    (wordCost : S → Fin M → Nat)
    (credits : S → Credits n) (leaders : S → Nat)
    (x0 : S) (Allowed : S → Prop)
    (hclosed : ∀ r, Allowed r → ∀ e y, outcome r e = .retry y → Allowed y)
    (hd : d ≤ s)
    (hmass : ∀ r, Allowed r →
      M ≤ 32 * successCount (macroStep outcome) (.active r) 1)
    (hcost : ∀ r, Allowed r →
      blockCostMass wordCost r ≤
        M * B0 n s +
          activeCount (macroStep outcome) (.active r) 1 * D n d)
    (hsuccessPhysical : ∀ r, Allowed r → ∀ e y,
      outcome r e = .success y →
        OnlySpends (credits x0) (credits y) ∧
        SpanChargedOnce 1 s (credits x0) (credits y) ∧
        leaders y < leaders x0) :
    ∀ r, Allowed r → ∀ T,
      renewalResidualNumerator outcome wordCost
          (fun y =>
            EpisodeTelescope.amortizedPotential (EScale n)
              (fun z => w (credits z)) leaders y)
          (EpisodeTelescope.amortizedPotential (EScale n)
            (fun z => w (credits z)) leaders x0)
          r T ≤
        M ^ T *
          EpisodeTelescope.amortizedPotential (EScale n)
            (fun z => w (credits z)) leaders x0 := by
  have hbudget :
      32 * B0 n s + (32 - 1) * D n d ≤ E n s := by
    simpa [K32] using K32_le_E (n := n) (s := s) (d := d) hd
  apply renewalResidualNumerator_le_on
    (outcome := outcome)
    (wordCost := wordCost)
    (terminalCredit := fun y =>
      EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) leaders y)
    (episodeCredit :=
      EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) leaders x0)
    (Allowed := Allowed) (hclosed := hclosed)
    (Q := 32) (base := B0 n s) (extra := D n d)
    (budget := E n s)
  · omega
  · exact hmass
  · exact hcost
  · exact hbudget
  · intro r hr e y hy
    rcases hsuccessPhysical r hr e y hy with
      ⟨hspend, hspan, hleader⟩
    exact original_span_funds_E
      credits leaders x0 y hspend hspan hleader


/-! ## Nontrivial finite test process

There is one successful macro symbol and one retry symbol.  Retry toggles the
state, so the scheduler can choose retry forever; there is no deterministic
finite retry cap.  Costs are positive (1 on success, 2 on retry), and terminal
credit depends on the actual successful state (2 from `cold`, 1 from `hot`).
-/
inductive ToyState where
  | cold
  | hot


/-- A concrete two-state block process with a state-changing retry symbol. -/
def toyOutcome : ToyState → Fin 2 → PayloadOutcome ToyState
  | .cold, e =>
      if e = (0 : Fin 2) then .success .cold else .retry .hot
  | .hot, e =>
      if e = (0 : Fin 2) then .success .hot else .retry .cold


/-- Positive block costs: one on success and two on retry. -/
def toyCost (_ : ToyState) (e : Fin 2) : Nat :=
  if e = (0 : Fin 2) then 1 else 2


/-- Different successful physical states retain different terminal credits. -/
def toyTerminalCredit : ToyState → Nat
  | .cold => 2
  | .hot => 1


/-- The actual state change made by a retry in the finite toy process. -/
def toyRetryNext : ToyState → ToyState
  | .cold => .hot
  | .hot => .cold


/-- Both concrete states have one successful symbol and one retry symbol. -/
theorem toy_stopped_counts (x : ToyState) :
    successCount (macroStep toyOutcome) (.active x) 1 = 1 ∧
    activeCount (macroStep toyOutcome) (.active x) 1 = 1 ∧
    failureCount (macroStep toyOutcome) (.active x) 1 = 0 := by
  cases x <;> decide


/-- The concrete block cost mass is three. -/
theorem toy_cost_mass (x : ToyState) :
    blockCostMass toyCost x = 3 := by
  cases x <;> decide


private theorem toy_terminal_le (x : ToyState) :
    toyTerminalCredit x ≤ 2 := by
  cases x <;> decide


/-- The retry scheduler symbol is available at every toy state and changes
state, so repeating symbol `1` gives arbitrarily many failed retries. -/
theorem toy_retry_edge (x : ToyState) :
    toyOutcome x (1 : Fin 2) = .retry (toyRetryNext x) := by
  cases x <;> rfl


/-- Concrete instance of the arbitrary-retry residual theorem:
`M=2`, `Q=2`, `base=1`, `extra=1`, exact block budget `3`, nonzero
successor-dependent terminal credit, and original episode credit `5`. -/
theorem toy_residual (x : ToyState) (T : Nat) :
    renewalResidualNumerator toyOutcome toyCost
        toyTerminalCredit 5 x T ≤
      2 ^ T * 5 := by
  apply renewalResidualNumerator_le_on
    (outcome := toyOutcome)
    (wordCost := toyCost)
    (terminalCredit := toyTerminalCredit)
    (episodeCredit := 5)
    (Allowed := fun _ => True) (hclosed := fun _ _ _ _ _ => trivial)
    (Q := 2) (base := 1) (extra := 1) (budget := 3)
  · omega
  · intro r _hr
    rcases toy_stopped_counts r with ⟨hs, _ha, _hf⟩
    rw [hs]
    omega
  · intro r _hr
    rcases toy_stopped_counts r with ⟨_hs, ha, _hf⟩
    rw [toy_cost_mass r, ha]
    omega
  · omega
  · intro r _hr e y _hy
    have ht := toy_terminal_le y
    omega
  · trivial

end FixedSpanRenewalPayload


namespace FixedSpanRenewalPayload

open FiniteUniformStoppingTree NonrenewableCredits

/-! ## Raw scheduler words, exact erasure, and partial-block costs

The payload process is a companion to `StopNode`, not a replacement for it.
Every raw interaction has unit cost while active. Successful payloads absorb
without further cost. A retry keeps the entire current state.
-/

/-- Extend the payload transition by absorbing success, retaining its state. -/
def payloadStep {S : Type} {n : Nat} (step : S → Fin n → PayloadOutcome S) :
    PayloadOutcome S → Fin n → PayloadOutcome S
  | .success y, _ => .success y
  | .retry x, e => step x e

/-- Execute an exact finite raw scheduler word, with success padding. -/
def runPayload {S : Type} {n : Nat} (step : S → Fin n → PayloadOutcome S) :
    PayloadOutcome S → List (Fin n) → PayloadOutcome S
  | q, [] => q
  | q, e :: es => runPayload step (payloadStep step q e) es

/-- Execute the same word using the repository's actual stopped transition. -/
def runStopped {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    StopNode S → List (Fin n) → StopNode S
  | q, [] => q
  | q, e :: es => runStopped step (stepNode step q e) es

/-- Physical interaction count of one finite word, including unfinished work. -/
def rawWordCost {S : Type} {n : Nat} (step : S → Fin n → PayloadOutcome S) :
    PayloadOutcome S → List (Fin n) → Nat
  | _, [] => 0
  | .success _, _ :: _ => 0
  | .retry x, e :: es => 1 + rawWordCost step (step x e) es

/-- Erasure commutes with one raw interaction. -/
theorem erase_payloadStep {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S) (e : Fin n) :
    erasePayload (payloadStep step q e) =
      stepNode (macroStep step) (erasePayload q) e := by
  cases q <;> rfl

/-- A successful word preserves its first-success successor through padding. -/
@[simp] theorem runPayload_success {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (y : S) (u : List (Fin n)) :
    runPayload step (.success y) u = .success y := by
  induction u with
  | nil => rfl
  | cons e es ih => exact ih

/-- Terminal padding carries no physical cost. -/
@[simp] theorem rawWordCost_success {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (y : S) (u : List (Fin n)) :
    rawWordCost step (.success y) u = 0 := by
  cases u <;> rfl

/-- Exact payload erasure for every raw word; no new stopped-node type occurs. -/
theorem erase_runPayload {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S) (u : List (Fin n)) :
    erasePayload (runPayload step q u) =
      runStopped (macroStep step) (erasePayload q) u := by
  induction u generalizing q with
  | nil => rfl
  | cons e es ih =>
      simp only [runPayload, runStopped, ih, erase_payloadStep]

/-- Cutting a word resumes from its exact retained outcome. -/
theorem runPayload_append {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S)
    (u v : List (Fin n)) :
    runPayload step q (u ++ v) = runPayload step (runPayload step q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons e es ih => exact ih (payloadStep step q e)

/-- A block cut conserves cost, even when the prefix ends halfway through
seeking. The suffix uses the actual residual state, not a canonical entrance. -/
theorem rawWordCost_append {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S)
    (u v : List (Fin n)) :
    rawWordCost step q (u ++ v) =
      rawWordCost step q u + rawWordCost step (runPayload step q u) v := by
  induction u generalizing q with
  | nil => simp [rawWordCost, runPayload]
  | cons e es ih =>
      cases q with
      | success y => simp [rawWordCost, runPayload, payloadStep]
      | retry x =>
          simp only [List.cons_append, rawWordCost, runPayload, payloadStep, ih]
          omega

/-- The precise retry-cut identity, retaining both partial cost and state. -/
theorem retry_cut_cost {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (x r : S)
    (u v : List (Fin n)) (hr : runPayload step (.retry x) u = .retry r) :
    rawWordCost step (.retry x) (u ++ v) =
      rawWordCost step (.retry x) u + rawWordCost step (.retry r) v := by
  rw [rawWordCost_append, hr]

/-- Exact scheduler sum, using the existing `allSchedules` enumeration in
reverse-word order. Reversal allows a first-symbol recurrence without changing
any word's multiplicity or the denominator `n^T`. -/
def wordSum (n T : Nat) (f : List (Fin n) → Nat) : Nat :=
  ((allSchedules n T).map (fun u => f u.reverse)).sum

private theorem sum_map_add {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem sum_flatMap_map {A B : Type} (xs : List A)
    (ys : A → List B) (f : B → Nat) :
    ((xs.flatMap ys).map f).sum = (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_swap {A : Type} {n : Nat} (xs : List A) (f : A → Fin n → Nat) :
    (xs.map (fun x => (List.ofFn (f x)).sum)).sum =
      (List.ofFn (fun e => (xs.map (fun x => f x e)).sum)).sum := by
  induction xs with
  | nil => simp [ofFn_sum_const]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [ofFn_sum_add]

/-- A finite product-space sum is a sum over the first symbol and suffix.
This also certifies the enumeration multiplicities, not just its cardinality. -/
theorem wordSum_succ (n T : Nat) (f : List (Fin n) → Nat) :
    wordSum n (T + 1) f =
      (List.ofFn (fun e : Fin n => wordSum n T (fun u => f (e :: u)))).sum := by
  unfold wordSum
  simp only [allSchedules, sum_flatMap_map, List.map_ofFn, Function.comp_def,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  exact sum_swap _ _

/-- Summing exact erased outcomes recovers the existing stopped-tree weights. -/
theorem wordSum_eq_treeWeight {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (weight : StopNode S → Nat)
    (q : PayloadOutcome S) (T : Nat) :
    wordSum n T (fun u => weight (erasePayload (runPayload step q u))) =
      treeWeight (macroStep step) weight (erasePayload q) T := by
  induction T generalizing q with
  | zero => simp [wordSum, allSchedules, runPayload, treeWeight]
  | succ T ih =>
      rw [wordSum_succ]
      simp only [runPayload, treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, erase_payloadStep]

/-- All physical active interactions, including incomplete seeking prefixes,
sum to the repository's exact truncated cost numerator. -/
theorem wordSum_cost_eq {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S) (T : Nat) :
    wordSum n T (rawWordCost step q) =
      truncatedActiveCostNumerator (macroStep step) (erasePayload q) T := by
  induction T generalizing q with
  | zero => simp [wordSum, allSchedules, rawWordCost, truncatedActiveCostNumerator]
  | succ T ih =>
      cases q with
      | success y => simp [wordSum, rawWordCost_success, sum_map_const,
          erasePayload, truncatedActiveCostNumerator]
      | retry x =>
          rw [wordSum_succ]
          simp only [rawWordCost]
          have hrow : ∀ e : Fin n,
              wordSum n T (fun u => 1 + rawWordCost step (step x e) u) =
                n ^ T + truncatedActiveCostNumerator (macroStep step)
                  (erasePayload (step x e)) T := by
            intro e
            change ((allSchedules n T).map (fun u =>
              1 + rawWordCost step (step x e) u.reverse)).sum = _
            rw [sum_map_add, sum_map_const, allSchedules_length, Nat.mul_one]
            exact congrArg (n ^ T + ·) (ih (step x e))
          rw [ofFn_sum_eq _ _ hrow, ofFn_sum_add, ofFn_sum_const]
          simp only [erasePayload, truncatedActiveCostNumerator, macroStep]
          rw [Nat.pow_succ]
          ac_rfl

/-- An index into the existing full enumeration of raw words. -/
def rawWord (n L : Nat) (i : Fin (n ^ L)) : List (Fin n) :=
  ((allSchedules n L)[i.val]'(by rw [allSchedules_length]; exact i.isLt)).reverse

private theorem sum_index {A : Type} {N : Nat} (xs : List A)
    (h : xs.length = N) (f : A → Nat) :
    (List.ofFn (fun i : Fin N => f (xs[i.val]'(by omega)))).sum = (xs.map f).sum := by
  subst N
  have hm := List.map_ofFn (f := fun i : Fin xs.length => xs[i.val]) (g := f)
  rw [List.ofFn_getElem] at hm
  exact congrArg List.sum hm.symm

/-- Indexing changes neither the finite-word sum nor its multiplicities. -/
theorem rawWord_sum (n L : Nat) (f : List (Fin n) → Nat) :
    (List.ofFn (fun i : Fin (n ^ L) => f (rawWord n L i))).sum = wordSum n L f := by
  exact sum_index (allSchedules n L) (allSchedules_length n L) (fun u => f u.reverse)

/-- Every macro symbol is an actual word of precisely `L` raw interactions. -/
theorem rawWord_length (n L : Nat) (i : Fin (n ^ L)) :
    (rawWord n L i).length = L := by
  unfold rawWord
  rw [List.length_reverse]
  exact allSchedules_schedule_length n L _ (List.getElem_mem _)

/-- A macro success retains the first physical success state; an unsuccessful
block retains the exact state after all `L` raw interactions. -/
def blockOutcome {S : Type} {n : Nat} (step : S → Fin n → PayloadOutcome S)
    (L : Nat) (x : S) (i : Fin (n ^ L)) : PayloadOutcome S :=
  runPayload step (.retry x) (rawWord n L i)

/-- Exact active physical cost of the same macro symbol. -/
def blockWordCost {S : Type} {n : Nat} (step : S → Fin n → PayloadOutcome S)
    (L : Nat) (x : S) (i : Fin (n ^ L)) : Nat :=
  rawWordCost step (.retry x) (rawWord n L i)

/-- Exact success-count transport, from raw depth `L` to one macro step. -/
theorem block_successCount_eq {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (L : Nat) (x : S) :
    successCount (macroStep (blockOutcome step L)) (.active x) 1 =
      successCount (macroStep step) (.active x) L := by
  rw [← successMass_eq_successCount]
  unfold successMass blockOutcome
  have hb : ∀ q : PayloadOutcome S, successBit q = successWeight (erasePayload q) := by
    intro q; cases q <;> rfl
  simp only [hb]
  rw [rawWord_sum n L (fun u => successWeight (erasePayload (runPayload step (.retry x) u))),
    wordSum_eq_treeWeight]
  rfl

/-- Exact active-count transport; retries include all nonsuccess residuals. -/
theorem block_activeCount_eq {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (L : Nat) (x : S) :
    activeCount (macroStep (blockOutcome step L)) (.active x) 1 =
      activeCount (macroStep step) (.active x) L := by
  rw [← retryMass_eq_activeCount]
  unfold retryMass blockOutcome
  have hb : ∀ q : PayloadOutcome S, retryBit q = activeWeight (erasePayload q) := by
    intro q; cases q <;> rfl
  simp only [hb]
  rw [rawWord_sum n L (fun u => activeWeight (erasePayload (runPayload step (.retry x) u))),
    wordSum_eq_treeWeight]
  rfl

/-- The macro cost is exactly the stopped physical numerator, so a block cut
cannot erase a partial waiting, seeking, or rearm stretch. -/
theorem block_cost_eq {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (L : Nat) (x : S) :
    blockCostMass (blockWordCost step L) x =
      truncatedActiveCostNumerator (macroStep step) (.active x) L := by
  unfold blockCostMass blockWordCost
  rw [rawWord_sum, wordSum_cost_eq]
  rfl

end FixedSpanRenewalPayload

namespace FixedSpanRenewalPayload
open FiniteUniformStoppingTree NonrenewableCredits

/-- Public one-block identity with the exact active-frontier credit `F*A0`.
The mass partition is derived from the retained stopped-tree API. -/
theorem one_block_residual
    {S : Type} {M Q base extra budget A0 : Nat}
    (outcome : S → Fin M → PayloadOutcome S) (cost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (x : S) (hQ : 0 < Q)
    (hmass : M ≤ Q * successCount (macroStep outcome) (.active x) 1)
    (hcost : blockCostMass cost x ≤
      M * base + activeCount (macroStep outcome) (.active x) 1 * extra)
    (hbudget : Q * base + (Q - 1) * extra ≤ budget)
    (hsuccess : ∀ e y, outcome x e = .success y → budget + terminalCredit y ≤ A0) :
    blockCostMass cost x + terminalCreditMass outcome terminalCredit x +
      activeCount (macroStep outcome) (.active x) 1 * A0 ≤ M * A0 := by
  rw [← successMass_eq_successCount] at hmass
  rw [← retryMass_eq_activeCount] at hcost ⊢
  have h := local_payload_residual_row outcome cost terminalCredit x hQ hmass hcost
    (mass_partition_from_stopped_tree outcome x) hbudget hsuccess
  rw [retryCreditMass_eq] at h
  exact h

/-- The invariant is needed only at retries, not at successful endpoints. -/
theorem runPayload_retry_closed {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (Allowed : S → Prop)
    (hclosed : ∀ x, Allowed x → ∀ e r, step x e = .retry r → Allowed r)
    (x y : S) (hx : Allowed x) (u : List (Fin n))
    (hy : runPayload step (.retry x) u = .retry y) : Allowed y := by
  induction u generalizing x with
  | nil => cases hy; exact hx
  | cons e es ih =>
      change runPayload step (step x e) es = .retry y at hy
      cases he : step x e with
      | success z => simp [he] at hy
      | retry r =>
          apply ih r (hclosed x hx e r he)
          simpa [he] using hy

/-- Lifting a one-interaction closure proof requires no extra macro invariant. -/
theorem block_retry_closed {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (L : Nat) (Allowed : S → Prop)
    (hclosed : ∀ x, Allowed x → ∀ e r, step x e = .retry r → Allowed r) :
    ∀ x, Allowed x → ∀ e r, blockOutcome step L x e = .retry r → Allowed r := by
  intro x hx e r hr
  exact runPayload_retry_closed step Allowed hclosed x r hx (rawWord n L e) hr

/-- A first traversal certificate is transported through arbitrary later
spending using the existing fixed-span theorem; the original start stays `x0`. -/
theorem original_span_funds_E_after_retries
    {S : Type} {n s : Nat} (credits : S → Credits n) (leaders : S → Nat)
    (x0 fresh y : S)
    (hfirst : OnlySpends (credits x0) (credits fresh))
    (hspan : SpanChargedOnce 1 s (credits x0) (credits fresh))
    (hafter : OnlySpends (credits fresh) (credits y))
    (hleader : leaders y < leaders x0) :
    E n s + EpisodeTelescope.amortizedPotential (EScale n)
      (fun z => w (credits z)) leaders y ≤
      EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) leaders x0 := by
  apply original_span_funds_E credits leaders x0 y
  · exact fun i hi => hfirst i (hafter i hi)
  · exact SpanChargedOnceAudit.fixed_span_survives_retries 1 s
      (credits x0) (credits fresh) (credits y) hspan hafter
  · exact hleader

/-- The accepted `E` budget feeds the existing global telescope, with the
actual endpoint residual and exactly scale `2304*n`. This bounds sums of
certified episode budgets; it does not identify them with pathwise random cost. -/
theorem E_episode_telescope {S : Type} {n : Nat}
    (next : S → S → Prop) (span : S → S → Nat)
    (credits : S → Credits n) (leaders : S → Nat)
    (hspend : ∀ x y, next x y → OnlySpends (credits x) (credits y))
    (hspan : ∀ x y, next x y → SpanChargedOnce 1 (span x y) (credits x) (credits y))
    (hleaders : ∀ x y, next x y → leaders y < leaders x)
    {start finish : S} {total : Nat}
    (trace : EpisodeTelescope.EpisodeTrace next (fun x y => E n (span x y))
      start total finish) :
    total + EpisodeTelescope.amortizedPotential (EScale n)
      (fun z => w (credits z)) leaders finish ≤
      EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) leaders start := by
  apply EpisodeTelescope.telescoping_with_residual (EScale n)
    (fun z => w (credits z)) leaders (trace := trace)
  intro x y hxy
  refine ⟨spend_monotone _ _ (hspend x y hxy), hleaders x y hxy, ?_⟩
  apply E_le_scale_of_span
  simpa only [SpanChargedOnce, Nat.one_mul] using hspan x y hxy

/-! ## Exact K2 consumer boundary

Here `physicalPayload` is defined from the actual K2 successor and success
guard. Closure of `GapPair` is discharged from the existing clean-boundary
proof. Uniform entrance/cost rows and original-start span credit remain
explicit application premises. No fresh tag, proof phase, or reseeding is used.
-/

open PPLLRepair LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance LDSinkTwoGapDeletion
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant

/-- Preserve the physical K2 successor even when the stopped tree erases it. -/
noncomputable def physicalPayload {n psi : Nat} (hpsi : psi > 0)
    (F : TwoGapFrame n) (x : AState n psi) (e : Fin n) : PayloadOutcome (AState n psi) := by
  classical
  exact if NoResetSuccess F (attemptStepConf hpsi F x e) then .success (postState hpsi F x e)
  else .retry (postState hpsi F x e)

/-- The payload transition erases to exactly the real physical block step. -/
theorem physicalPayload_erases {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n) :
    macroStep (physicalPayload hpsi F) = physicalBlockStep hpsi F := by
  funext x e
  classical
  rw [physicalBlockStep_normal_form]
  unfold macroStep physicalPayload
  split <;> rfl

/-- Successful payloads contain precisely the actual post-interaction state. -/
theorem physicalPayload_success {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n)
    (x y : AState n psi) (e : Fin n) (hy : physicalPayload hpsi F x e = .success y) :
    y = postState hpsi F x e ∧ NoResetSuccess F y.conf := by
  classical
  unfold physicalPayload at hy
  split at hy
  · cases hy
    exact ⟨rfl, by assumption⟩
  · cases hy

/-- Actual gap closure includes absorption/rearm residuals, supplied by the
proved K2 clean-boundary result rather than a carried restart field. -/
theorem physicalPayload_retry_closed {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n) :
    ∀ x, GapPair hpsi F x → ∀ e y,
      physicalPayload hpsi F x e = .retry y → GapPair hpsi F y := by
  intro x hx e y hy
  have he := congrArg erasePayload hy
  change macroStep (physicalPayload hpsi F) x e = .active y at he
  rw [physicalPayload_erases] at he
  exact LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F) x e y hx he

/-- Exact physical block closure, without resetting any internal control tag. -/
theorem physical_block_retry_closed {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) :
    ∀ x, GapPair hpsi F x → ∀ e y,
      blockOutcome (physicalPayload hpsi F) L x e = .retry y → GapPair hpsi F y :=
  block_retry_closed _ L _ (physicalPayload_retry_closed hpsi F)

/-- Discharged `1/16` physical race suffix plus a uniform `1/2` entrance row
produces the actual macro `1/32` row on every retained `GapPair` state. -/
theorem physical_block_mass {n psi : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n) (HE : Nat)
    (hEntrance : ∀ r, GapPair hpsi F r → n ^ HE ≤
      2 * successCount (entranceStep hpsi F) (.active r) HE) :
    ∀ r, GapPair hpsi F r → n ^ (HE + 4 * n) ≤
      32 * successCount (macroStep (blockOutcome (physicalPayload hpsi F)
        (HE + 4 * n))) (.active r) 1 := by
  intro r hr
  rw [block_successCount_eq, physicalPayload_erases]
  exact LDSinkTwoGapArrivalRaceMass.physical_entrance_then_race_mass hpsi F r hr HE
    (hEntrance r hr)

/-- Physical leaders are counted by the repository's finite Boolean sum. -/
def physicalLeaders {n psi : Nat} (x : AState n psi) : Nat :=
  w (fun i => (x.conf i).leader)

/-- The actual retained retry carrier for one fixed original episode start.
It uses the existing reachability relation and the unchanged physical step. -/
def PhysicalRetryCarrier {n psi : Nat} (hpsi : psi > 0) (F : TwoGapFrame n)
    (x0 : AState n psi) : AState n psi → Prop :=
  ActiveReach (physicalBlockStep hpsi F) (fun x => x = x0)

/-- The original physical seed belongs to its retry carrier. -/
theorem physicalRetryCarrier_start {n psi : Nat} (hpsi : psi > 0)
    (F : TwoGapFrame n) (x0 : AState n psi) : PhysicalRetryCarrier hpsi F x0 x0 :=
  ActiveReach.base rfl

/-- Raw retries preserve reachability from the same start; no credit or phase
is recomputed when extending this carrier. -/
theorem physicalRetryCarrier_closed {n psi : Nat} (hpsi : psi > 0)
    (F : TwoGapFrame n) (x0 : AState n psi) :
    ∀ r, PhysicalRetryCarrier hpsi F x0 r → ∀ e y,
      physicalPayload hpsi F r e = .retry y → PhysicalRetryCarrier hpsi F x0 y := by
  intro r hr e y hy
  have he := congrArg erasePayload hy
  change macroStep (physicalPayload hpsi F) r e = .active y at he
  rw [physicalPayload_erases] at he
  exact ActiveReach.next e hr he

/-- Every retained retry state still has the actual gap-pair invariant. -/
theorem physicalRetryCarrier_gapPair {n psi : Nat} (hpsi : psi > 0)
    (F : TwoGapFrame n) (x0 : AState n psi) (hstart : GapPair hpsi F x0)
    (r : AState n psi) (hr : PhysicalRetryCarrier hpsi F x0 r) : GapPair hpsi F r := by
  apply ActiveReach.invariant (physicalBlockStep hpsi F) (fun x => x = x0)
    (GapPair hpsi F) _ _ r hr
  · intro x hx; subst x; exact hstart
  · intro x e y hx hy
    exact LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
      (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F) x e y hx hy

/-- Conditional application to real K2, with exact word costs and physical
successor payloads already supplied. Remaining rows are uniform entrance,
physical truncated cost (including partial service), and original-start credit
and leader descent for successful words. It proves no unconditional complexity
claim for the paper. -/
theorem physical_fixed_span_renewal_residual {n psi s d : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n) (HE : Nat)
    (credits : AState n psi → Credits n) (x0 : AState n psi)
    (hstart : GapPair hpsi F x0)
    (hd : d ≤ s)
    (hEntrance : ∀ r, PhysicalRetryCarrier hpsi F x0 r → n ^ HE ≤
      2 * successCount (entranceStep hpsi F) (.active r) HE)
    (hcost : ∀ r, PhysicalRetryCarrier hpsi F x0 r →
      truncatedActiveCostNumerator (physicalBlockStep hpsi F) (.active r) (HE + 4 * n) ≤
        n ^ (HE + 4 * n) * B0 n s +
          activeCount (physicalBlockStep hpsi F) (.active r) (HE + 4 * n) * D n d)
    (hsuccess : ∀ r, PhysicalRetryCarrier hpsi F x0 r → ∀ e y,
      blockOutcome (physicalPayload hpsi F) (HE + 4 * n) r e = .success y →
        OnlySpends (credits x0) (credits y) ∧
        SpanChargedOnce 1 s (credits x0) (credits y) ∧
        physicalLeaders y < physicalLeaders x0) :
    ∀ r, PhysicalRetryCarrier hpsi F x0 r → ∀ T,
      renewalResidualNumerator
        (blockOutcome (physicalPayload hpsi F) (HE + 4 * n))
        (blockWordCost (physicalPayload hpsi F) (HE + 4 * n))
        (EpisodeTelescope.amortizedPotential (EScale n) (fun z => w (credits z))
          physicalLeaders)
        (EpisodeTelescope.amortizedPotential (EScale n) (fun z => w (credits z))
          physicalLeaders x0) r T ≤
      (n ^ (HE + 4 * n)) ^ T * EpisodeTelescope.amortizedPotential (EScale n)
        (fun z => w (credits z)) physicalLeaders x0 := by
  apply fixed_span_E_renewal_residual _ _ credits physicalLeaders x0
    (PhysicalRetryCarrier hpsi F x0)
    (block_retry_closed _ _ _ (physicalRetryCarrier_closed hpsi F x0)) hd
  · intro r hr
    rw [block_successCount_eq, physicalPayload_erases]
    exact LDSinkTwoGapArrivalRaceMass.physical_entrance_then_race_mass hpsi F r
      (physicalRetryCarrier_gapPair hpsi F x0 hstart r hr) HE (hEntrance r hr)
  · intro r hr
    rw [block_cost_eq, block_activeCount_eq, physicalPayload_erases]
    exact hcost r hr
  · exact hsuccess

end FixedSpanRenewalPayload

namespace FixedSpanRenewalPayload
open FiniteUniformStoppingTree NonrenewableCredits

/-! ## Finite process acceptance witnesses

These are concrete two-state processes, not claimed to instantiate K2's
unproved span or cost rows. They test nonconstant successful residuals,
indefinitely available retries, exact raw-word enumeration, and a block cut
inside unfinished work.
-/

/-- The stopped success value cannot reconstruct two different terminal
credits. This is the exact payload-erasure obstruction in the old interface. -/
theorem toy_terminal_credit_not_on_erasure :
    ¬ ∃ f : StopNode ToyState → Nat, ∀ x : ToyState,
      terminalWordCredit toyTerminalCredit (toyOutcome x 0) =
        f (erasePayload (toyOutcome x 0)) := by
  rintro ⟨f, hf⟩
  have hc := hf .cold
  have hh := hf .hot
  change 2 = f .success at hc
  change 1 = f .success at hh
  omega

/-- The state reached after choosing the available retry symbol repeatedly. -/
def toyRetryTrace : ToyState → Nat → ToyState
  | x, 0 => x
  | x, T + 1 => toyRetryTrace (toyRetryNext x) T

/-- Every finite raw horizon has a still-active word. No deterministic retry
cap is hidden by the finite-depth induction. -/
theorem toy_arbitrarily_many_retries (x : ToyState) (T : Nat) :
    runPayload toyOutcome (.retry x) (List.replicate T (1 : Fin 2)) =
      .retry (toyRetryTrace x T) := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [List.replicate_succ, runPayload, payloadStep, toy_retry_edge, toyRetryTrace]
      exact ih (toyRetryNext x)

/-- Cutting after the first unsuccessful interaction keeps the spent unit
and the changed state. The next symbol succeeds with the hot-state credit. -/
theorem toy_partial_block_cost :
    runPayload toyOutcome (.retry .cold) [1] = .retry .hot ∧
    rawWordCost toyOutcome (.retry .cold) [1] = 1 ∧
    runPayload toyOutcome (.retry .cold) [1, 0] = .success .hot ∧
    rawWordCost toyOutcome (.retry .cold) [1, 0] = 2 ∧
    terminalWordCredit toyTerminalCredit
      (runPayload toyOutcome (.retry .cold) [1, 0]) = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A fully enumerated two-interaction block: four words, three successes,
one retry, and six active interaction units. -/
theorem toy_raw_block_rows (x : ToyState) :
    successCount (macroStep (blockOutcome toyOutcome 2)) (.active x) 1 = 3 ∧
    activeCount (macroStep (blockOutcome toyOutcome 2)) (.active x) 1 = 1 ∧
    blockCostMass (blockWordCost toyOutcome 2) x = 6 := by
  rw [block_successCount_eq, block_activeCount_eq, block_cost_eq]
  cases x <;> decide

/-- Nonzero costs and actual raw block evaluation instantiate every row of
the arbitrary-depth renewal bound. Both successful terminal credits occur. -/
theorem toy_raw_block_residual (x : ToyState) (T : Nat) :
    renewalResidualNumerator (blockOutcome toyOutcome 2) (blockWordCost toyOutcome 2)
      toyTerminalCredit 6 x T ≤ 4 ^ T * 6 := by
  apply renewalResidualNumerator_le_on
    (Allowed := fun _ => True) (hclosed := fun _ _ _ _ _ => trivial)
    (Q := 2) (base := 1) (extra := 2) (budget := 4)
  · decide
  · intro r _
    rw [(toy_raw_block_rows r).1]
    decide
  · intro r _
    rw [(toy_raw_block_rows r).2.1, (toy_raw_block_rows r).2.2]
    decide
  · decide
  · intro _ _ _ y _
    have h := toy_terminal_le y
    omega
  · trivial

/-- Exact concrete one-block residual: the six units of raw cost, five units
of successful payload credit, and one full original credit sum to seventeen. -/
theorem toy_raw_exact_residual :
    blockCostMass (blockWordCost toyOutcome 2) .cold = 6 ∧
    terminalCreditMass (blockOutcome toyOutcome 2) toyTerminalCredit .cold = 5 ∧
    activeCount (macroStep (blockOutcome toyOutcome 2)) (.active .cold) 1 = 1 ∧
    renewalResidualNumerator (blockOutcome toyOutcome 2) (blockWordCost toyOutcome 2)
      toyTerminalCredit 6 .cold 1 = 17 := by
  decide

end FixedSpanRenewalPayload

namespace FixedSpanRenewalPayload
open FiniteUniformStoppingTree NonrenewableCredits

/-- Every active interaction is counted once, so an `L`-symbol word costs at
most `L`, regardless of unfinished internal service phases. -/
theorem rawWordCost_le_length {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (q : PayloadOutcome S) (u : List (Fin n)) :
    rawWordCost step q u ≤ u.length := by
  induction u generalizing q with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
      cases q with
      | success y => exact Nat.zero_le _
      | retry x =>
          have h := ih (step x e)
          change 1 + rawWordCost step (step x e) es ≤ es.length + 1
          omega

/-- A fixed raw horizon gives an unconditional physical cost bound on the
whole block. Partial service interactions are included, not discarded. -/
theorem block_cost_le_horizon {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (L : Nat) (x : S) :
    blockCostMass (blockWordCost step L) x ≤ n ^ L * L := by
  apply Nat.le_trans (ofFn_sum_le _ (fun _ => L) ?_)
    (Nat.le_of_eq (ofFn_sum_const (n ^ L) L))
  intro e
  exact Nat.le_trans (rawWordCost_le_length step (.retry x) (rawWord n L e))
    (Nat.le_of_eq (rawWord_length n L e))

/-- At the intended entrance horizon `32*n*s`, the complete raw block length
is exactly `B0`. Consequently the requested cost row is automatic, even before
using the nonnegative retry-service allowance `F*D`. The unresolved requirement
is that the success-mass estimate hold uniformly at this same horizon. -/
theorem physical_fixed_horizon_cost_row {n psi s d : Nat}
    (hpsi : psi > 0) (F : LDTwoGapFrame.TwoGapFrame n)
    (r : LDSinkTwoGapNoResetKernel.AState n psi) :
    truncatedActiveCostNumerator (LDSinkTwoGapDeletionWired.physicalBlockStep hpsi F)
      (.active r) (32 * n * s + 4 * n) ≤
      n ^ (32 * n * s + 4 * n) * B0 n s +
        activeCount (LDSinkTwoGapDeletionWired.physicalBlockStep hpsi F)
          (.active r) (32 * n * s + 4 * n) * D n d := by
  have h := block_cost_le_horizon (physicalPayload hpsi F) (32 * n * s + 4 * n) r
  rw [block_cost_eq, physicalPayload_erases] at h
  have he : 32 * n * s + 4 * n = B0 n s := by
    unfold B0
    simp only [Nat.mul_add]
    ac_rfl
  calc
    _ ≤ n ^ (32 * n * s + 4 * n) * (32 * n * s + 4 * n) := h
    _ = n ^ (32 * n * s + 4 * n) * B0 n s := by rw [he]
    _ ≤ _ := Nat.le_add_right _ _

open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant
open LDSinkTwoGapEntrance

/-- A physical specialization with the entire fixed-block cost row discharged.
Uniform entrance mass on the original retry carrier and original-start span
credit remain explicit. This does not claim those K2 premises are available. -/
theorem physical_fixed_horizon_renewal_residual {n psi s d : Nat}
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (credits : AState n psi → Credits n) (x0 : AState n psi)
    (hstart : GapPair hpsi F x0) (hd : d ≤ s)
    (hEntrance : ∀ r, PhysicalRetryCarrier hpsi F x0 r → n ^ (32 * n * s) ≤
      2 * successCount (entranceStep hpsi F) (.active r) (32 * n * s))
    (hsuccess : ∀ r, PhysicalRetryCarrier hpsi F x0 r → ∀ e y,
      blockOutcome (physicalPayload hpsi F) (32 * n * s + 4 * n) r e = .success y →
        OnlySpends (credits x0) (credits y) ∧
        SpanChargedOnce 1 s (credits x0) (credits y) ∧
        physicalLeaders y < physicalLeaders x0) :
    ∀ T, renewalResidualNumerator
      (blockOutcome (physicalPayload hpsi F) (32 * n * s + 4 * n))
      (blockWordCost (physicalPayload hpsi F) (32 * n * s + 4 * n))
      (EpisodeTelescope.amortizedPotential (EScale n) (fun z => w (credits z)) physicalLeaders)
      (EpisodeTelescope.amortizedPotential (EScale n) (fun z => w (credits z))
        physicalLeaders x0) x0 T ≤
      (n ^ (32 * n * s + 4 * n)) ^ T *
        EpisodeTelescope.amortizedPotential (EScale n) (fun z => w (credits z))
          physicalLeaders x0 := by
  exact physical_fixed_span_renewal_residual hpsi F (32 * n * s) credits x0 hstart hd
    hEntrance (fun r _ => physical_fixed_horizon_cost_row hpsi F r) hsuccess x0
    (physicalRetryCarrier_start hpsi F x0)

end FixedSpanRenewalPayload

namespace FixedSpanRenewalPayload
open FiniteUniformStoppingTree NonrenewableCredits

/-- A finite witness with separate active and successful physical states.
This is an independent finite process, not an asserted K2 implementation. -/
inductive FundingState where
  | cold | hot | doneCold | doneHot
  deriving DecidableEq

/-- The retained retry carrier excludes completed states. -/
def fundingAllowed (x : FundingState) : Prop := x = .cold ∨ x = .hot

/-- One raw symbol succeeds; the other retries from the changed active state. -/
def fundingRaw : FundingState → Fin 2 → PayloadOutcome FundingState
  | .cold, e => if e = 0 then .success .doneCold else .retry .hot
  | .hot, e => if e = 0 then .success .doneHot else .retry .cold
  | .doneCold, _ => .success .doneCold
  | .doneHot, _ => .success .doneHot

/-- Two initial site credits; different physical successes retain different
nonzero/zero credit stocks. Active retries leave the original stock intact. -/
def fundingCredits : FundingState → Credits 2
  | .cold | .hot => fun _ => true
  | .doneCold => fun i => decide (i = 0)
  | .doneHot => fun _ => false

/-- The concrete process loses one of its two leaders at either success. -/
def fundingLeaders : FundingState → Nat
  | .cold | .hot => 2
  | .doneCold | .doneHot => 1

/-- Both active states satisfy raw retry closure; successful endpoints are
outside the carrier, as in an elimination episode. -/
theorem funding_raw_closed : ∀ x, fundingAllowed x → ∀ e y,
    fundingRaw x e = .retry y → fundingAllowed y := by
  intro x hx e y hy
  rcases hx with rfl | rfl <;>
    (simp only [fundingRaw] at hy; split at hy)
  · cases hy
  · cases hy; exact Or.inr rfl
  · cases hy
  · cases hy; exact Or.inl rfl

/-- All fixed-span funding premises are discharged on both retained states
and every two-symbol word. In particular, this is not a vacuous conditional. -/
theorem funding_rows :
    (∀ r, fundingAllowed r → 4 ≤
      32 * successCount (macroStep (blockOutcome fundingRaw 2)) (.active r) 1) ∧
    (∀ r, fundingAllowed r → blockCostMass (blockWordCost fundingRaw 2) r ≤
      4 * B0 2 2 + activeCount (macroStep (blockOutcome fundingRaw 2)) (.active r) 1 * D 2 1) ∧
    (∀ r, fundingAllowed r → ∀ e y,
      blockOutcome fundingRaw 2 r e = .success y →
        OnlySpends (fundingCredits .cold) (fundingCredits y) ∧
        SpanChargedOnce 1 2 (fundingCredits .cold) (fundingCredits y) ∧
        fundingLeaders y < fundingLeaders .cold) := by
  constructor
  · intro r hr
    rcases hr with rfl | rfl <;> decide
  constructor
  · intro r hr
    rcases hr with rfl | rfl <;> decide
  · intro r hr e y
    have he : e = (0 : Fin 4) ∨ e = (1 : Fin 4) ∨
        e = (2 : Fin 4) ∨ e = (3 : Fin 4) := by
      simp only [Fin.ext_iff]
      change e.val = 0 ∨ e.val = 1 ∨ e.val = 2 ∨ e.val = 3
      have hb : e.val < 4 := e.isLt
      omega
    rcases hr with rfl | rfl <;> cases y <;>
      rcases he with rfl | rfl | rfl | rfl
    all_goals unfold OnlySpends SpanChargedOnce; decide


/-- A checked instance of the actual project-facing `E` substitution theorem,
with exact raw blocks, nonconstant terminal credit, no deterministic retry cap,
and the same original start for every finite macro depth. -/
theorem funding_fixed_span_residual (T : Nat) :
    renewalResidualNumerator (blockOutcome fundingRaw 2) (blockWordCost fundingRaw 2)
      (EpisodeTelescope.amortizedPotential (EScale 2) (fun z => w (fundingCredits z))
        fundingLeaders)
      (EpisodeTelescope.amortizedPotential (EScale 2) (fun z => w (fundingCredits z))
        fundingLeaders .cold) .cold T ≤ 4 ^ T * 18432 := by
  have h := fixed_span_E_renewal_residual (blockOutcome fundingRaw 2)
    (blockWordCost fundingRaw 2) fundingCredits fundingLeaders .cold fundingAllowed
    (block_retry_closed fundingRaw 2 fundingAllowed funding_raw_closed)
    (by decide : 1 ≤ 2) funding_rows.1 funding_rows.2.1 funding_rows.2.2 .cold
    (Or.inl rfl) T
  exact h

/-- Distinct successful physical states really supply different global
residuals, while the active original-start credit is `18432`. -/
theorem funding_concrete_credits :
    EpisodeTelescope.amortizedPotential (EScale 2) (fun z => w (fundingCredits z))
      fundingLeaders .cold = 18432 ∧
    EpisodeTelescope.amortizedPotential (EScale 2) (fun z => w (fundingCredits z))
      fundingLeaders .doneCold = 9216 ∧
    EpisodeTelescope.amortizedPotential (EScale 2) (fun z => w (fundingCredits z))
      fundingLeaders .doneHot = 4608 ∧
    E 2 2 = 8704 := by
  decide

end FixedSpanRenewalPayload

namespace FixedSpanRenewalPayload
open FiniteUniformStoppingTree NonrenewableCredits

/-- Every successful finite word has a genuine first-success transition
from the retained retry carrier; terminal padding never invents a state. -/
theorem runPayload_success_origin {S : Type} {n : Nat}
    (step : S → Fin n → PayloadOutcome S) (Allowed : S → Prop)
    (hclosed : ∀ x, Allowed x → ∀ e r, step x e = .retry r → Allowed r)
    (x y : S) (hx : Allowed x) (u : List (Fin n))
    (hy : runPayload step (.retry x) u = .success y) :
    ∃ r, Allowed r ∧ ∃ e, step r e = .success y := by
  induction u generalizing x with
  | nil => cases hy
  | cons e es ih =>
      change runPayload step (step x e) es = .success y at hy
      cases he : step x e with
      | success z =>
          rw [he, runPayload_success] at hy
          cases hy
          exact ⟨x, hx, e, he⟩
      | retry r =>
          apply ih r (hclosed x hx e r he)
          simpa [he] using hy

/-- The final physical successor is the actual K2 post-state of a reachable
predecessor, together with the real `NoResetSuccess` guard. -/
theorem physical_block_success_origin {n psi : Nat} (hpsi : psi > 0)
    (F : LDTwoGapFrame.TwoGapFrame n) (x0 r y : LDSinkTwoGapNoResetKernel.AState n psi)
    (hr : PhysicalRetryCarrier hpsi F x0 r) (L : Nat) (e : Fin (n ^ L))
    (hy : blockOutcome (physicalPayload hpsi F) L r e = .success y) :
    ∃ pre, PhysicalRetryCarrier hpsi F x0 pre ∧ ∃ edge,
      y = LDSinkTwoGapDeletionWired.postState hpsi F pre edge ∧
      LDSinkTwoGapNoResetKernel.NoResetSuccess F y.conf := by
  obtain ⟨pre, hp, edge, he⟩ := runPayload_success_origin (physicalPayload hpsi F)
    (PhysicalRetryCarrier hpsi F x0) (physicalRetryCarrier_closed hpsi F x0)
    r y hr (rawWord n L e) hy
  exact ⟨pre, hp, edge, physicalPayload_success hpsi F pre y edge he⟩

/-- Actual accumulated macro-word costs, with no cost after success. -/
def weightedWordCost {S : Type} {M : Nat}
    (step : S → Fin M → PayloadOutcome S) (cost : S → Fin M → Nat) :
    PayloadOutcome S → List (Fin M) → Nat
  | _, [] => 0
  | .success _, _ :: _ => 0
  | .retry x, e :: es => cost x e + weightedWordCost step cost (step x e) es

/-- A successful frontier retains its actual state's terminal credit; an
active frontier retains the same original-start credit at every retry depth. -/
def frontierCredit {S : Type} (terminalCredit : S → Nat) (A0 : Nat) :
    PayloadOutcome S → Nat
  | .success y => terminalCredit y
  | .retry _ => A0

private theorem wordSum_add (n T : Nat) (f g : List (Fin n) → Nat) :
    wordSum n T (fun u => f u + g u) = wordSum n T f + wordSum n T g :=
  sum_map_add _ _ _

private theorem wordSum_const (n T c : Nat) :
    wordSum n T (fun _ => c) = n ^ T * c := by
  unfold wordSum
  rw [sum_map_const, allSchedules_length]

private theorem weightedWordCost_success {S : Type} {M : Nat}
    (step : S → Fin M → PayloadOutcome S) (cost : S → Fin M → Nat)
    (y : S) (u : List (Fin M)) : weightedWordCost step cost (.success y) u = 0 := by
  cases u <;> rfl

/-- Kernel-checked finite-word semantics of the renewal recurrence: its
numerator is exactly accumulated physical costs plus the actual terminal
payload credit, or the unchanged `A0` on unfinished words. -/
theorem renewalResidual_eq_finite_word_sum {S : Type} {M : Nat}
    (step : S → Fin M → PayloadOutcome S) (cost : S → Fin M → Nat)
    (terminalCredit : S → Nat) (A0 : Nat) (x : S) (T : Nat) :
    renewalResidualNumerator step cost terminalCredit A0 x T =
      wordSum M T (fun u => weightedWordCost step cost (.retry x) u +
        frontierCredit terminalCredit A0 (runPayload step (.retry x) u)) := by
  have hall : ∀ T (q : PayloadOutcome S),
      wordSum M T (fun u => weightedWordCost step cost q u +
        frontierCredit terminalCredit A0 (runPayload step q u)) =
      match q with
      | .success y => M ^ T * terminalCredit y
      | .retry r => renewalResidualNumerator step cost terminalCredit A0 r T := by
    intro T q
    induction T generalizing q with
    | zero => cases q <;> simp [wordSum, allSchedules, weightedWordCost,
        runPayload, frontierCredit, renewalResidualNumerator]
    | succ T ih =>
        cases q with
        | success y => simp only [weightedWordCost_success, runPayload_success,
            frontierCredit, Nat.zero_add, wordSum_const]
        | retry r =>
            rw [wordSum_succ]
            simp only [weightedWordCost, runPayload, payloadStep, renewalResidualNumerator]
            apply ofFn_sum_eq
            intro e
            simp only [Nat.add_assoc]
            rw [wordSum_add, wordSum_const, ih]
  exact (hall T (.retry x)).symm

end FixedSpanRenewalPayload

#print axioms FixedSpanRenewalPayload.one_block_residual
#print axioms FixedSpanRenewalPayload.renewalResidualNumerator_le_on
#print axioms FixedSpanRenewalPayload.renewalResidual_eq_finite_word_sum
#print axioms FixedSpanRenewalPayload.fixed_span_E_renewal_residual
#print axioms FixedSpanRenewalPayload.E_episode_telescope
#print axioms FixedSpanRenewalPayload.block_successCount_eq
#print axioms FixedSpanRenewalPayload.block_activeCount_eq
#print axioms FixedSpanRenewalPayload.block_cost_eq
#print axioms FixedSpanRenewalPayload.retry_cut_cost
#print axioms FixedSpanRenewalPayload.physicalPayload_erases
#print axioms FixedSpanRenewalPayload.physical_block_success_origin
#print axioms FixedSpanRenewalPayload.physicalRetryCarrier_gapPair
#print axioms FixedSpanRenewalPayload.physical_fixed_horizon_cost_row
#print axioms FixedSpanRenewalPayload.physical_fixed_horizon_renewal_residual
#print axioms FixedSpanRenewalPayload.toy_terminal_credit_not_on_erasure
#print axioms FixedSpanRenewalPayload.toy_arbitrarily_many_retries
#print axioms FixedSpanRenewalPayload.toy_raw_exact_residual
#print axioms FixedSpanRenewalPayload.funding_fixed_span_residual
