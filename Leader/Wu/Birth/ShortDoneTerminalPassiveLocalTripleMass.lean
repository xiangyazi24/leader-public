import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleProducer
import Leader.Wu.Scheduler.FixedSpanRenewalPayload


namespace BirthShortDoneTerminalPassiveLocal3Mass


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthWaitClockMass BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing BirthWaitClockMass.ResetEntry
open BirthShortWaitDomainWitness BirthShortWaitRawRing
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Count
open BirthShortDoneTerminalPassiveLocal3Producer
open FiniteUniformStoppingTree ControlledSchedulerMass


set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false


variable {psi kappa tau n : Nat}


/-- Concrete consumer target for the recursive physical event.


In the entry branch, `pre` is an actually executed TerminalHost prefix and
`post` is completely unrestricted.  In the cap branch, exactly `pre` has been
executed: `e` is still the current scheduler edge, so `RowCap2` is tested on
the physical configuration before the cap row is executed. -/
def Local3PhysicalEndpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (es : List (Fin n)) : Prop :=
  (exists pre post,
    es = pre ++ post /\
    OrderedWaitEntry2 hn
      (pre.foldl (hostStep hpsi h2 ring) C)) \/
  exists pre e post,
    es = pre ++ (e :: post) /\
    SafeLine3Edge hn e /\
    InternalLine3Edge hn e /\
    RowCap2 hpsi h2 kappa ring
      (pre.foldl (hostStep hpsi h2 ring) C) e


/-- Prefixing one actually executed host row transports a concrete endpoint
witness back to the preceding physical configuration. -/
private theorem endpoint_prepend
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) (es : List (Fin n))
    (h : Local3PhysicalEndpoint hpsi h2 hn kappa tau ring
      (hostStep hpsi h2 ring C e) es) :
    Local3PhysicalEndpoint hpsi h2 hn kappa tau ring C (e :: es) := by
  rcases h with hentry | hcap
  · rcases hentry with ⟨pre, post, hword, hwait⟩
    refine Or.inl ⟨e :: pre, post, ?_, ?_⟩
    · rw [hword]
      rfl
    · exact hwait
  · rcases hcap with ⟨pre, ec, post, hword, hsafe, hint, hrow⟩
    refine Or.inr ⟨e :: pre, ec, post, ?_, hsafe, hint, ?_⟩
    · rw [hword]
      rfl
    · exact hrow


/-- A current cap witness is consumed without executing the cap edge. -/
private theorem endpoint_cap_here
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) (tail : List (Fin n))
    (hcap : Local3CapNow hpsi h2 hn kappa tau ring C e) :
    Local3PhysicalEndpoint hpsi h2 hn kappa tau ring C (e :: tail) := by
  rcases hcap with ⟨_, hsafe, hint, hrow⟩
  exact Or.inr ⟨[], e, tail, rfl, hsafe, hint, hrow⟩


/-- Consume the post-p0 recursive event into an actual executed-prefix entry
or an actual current physical cap. -/
private theorem afterP0_physical_endpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (es : List (Fin n))
    (h : Local3AfterP0 hpsi h2 hn kappa tau ring C es) :
    Local3PhysicalEndpoint hpsi h2 hn kappa tau ring C es := by
  induction es generalizing C with
  | nil =>
      have hf : False := by
        simpa only [Local3AfterP0] using h
      exact hf.elim
  | cons e es ih =>
      simp only [Local3AfterP0] at h
      rcases h with hcap | h
      · exact endpoint_cap_here hpsi h2 hn kappa tau ring C e es hcap
      rcases h with hentry | h
      · rcases hentry with ⟨_, _, _, _, hwait⟩
        rcases hwait with ⟨_, hordered⟩
        exact Or.inl ⟨[e], es, rfl, hordered⟩
      rcases h with hp0 | hout
      · rcases hp0 with ⟨_, _, _, _, hnext⟩
        exact endpoint_prepend hpsi h2 hn kappa tau ring C e es
          (ih (C := hostStep hpsi h2 ring C e) hnext)
      · rcases hout with ⟨_, _, _, hnext⟩
        exact endpoint_prepend hpsi h2 hn kappa tau ring C e es
          (ih (C := hostStep hpsi h2 ring C e) hnext)


/-- Nonrecursive consumer of the accepted full-host prefix event.


The conclusion exposes either an executed prefix whose literal `hostStep`
fold reaches `OrderedWaitEntry2`, or a prefix after which the next internal
edge is physically `RowCap2`.  The cap edge itself is not folded. -/
theorem Local3EntryOrCap_physical_endpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (es : List (Fin n))
    (h : Local3EntryOrCap hpsi h2 hn kappa tau ring C es) :
    Local3PhysicalEndpoint hpsi h2 hn kappa tau ring C es := by
  induction es generalizing C with
  | nil =>
      have hf : False := by
        simpa only [Local3EntryOrCap] using h
      exact hf.elim
  | cons e es ih =>
      simp only [Local3EntryOrCap] at h
      rcases h with hcap | h
      · exact endpoint_cap_here hpsi h2 hn kappa tau ring C e es hcap
      rcases h with hp0 | h
      · rcases hp0 with ⟨_, _, _, _, hnext⟩
        exact endpoint_prepend hpsi h2 hn kappa tau ring C e es
          (afterP0_physical_endpoint hpsi h2 hn kappa tau ring
            (hostStep hpsi h2 ring C e) es hnext)
      rcases h with hp1 | hout
      · rcases hp1 with ⟨_, _, _, _, hnext⟩
        exact endpoint_prepend hpsi h2 hn kappa tau ring C e es
          (ih (C := hostStep hpsi h2 ring C e) hnext)
      · rcases hout with ⟨_, _, _, hnext⟩
        exact endpoint_prepend hpsi h2 hn kappa tau ring C e es
          (ih (C := hostStep hpsi h2 ring C e) hnext)


/-- Direct successful-matcher consumer, now ending in a concrete physical
prefix witness rather than the recursive event itself. -/
theorem twoCross_success_physical_endpoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hline : LocalLine3 hpsi hn C)
    (es : List (Fin n))
    (hs : runWord (twoCrossStep hn) (.active false) es = .success) :
    Local3PhysicalEndpoint hpsi h2 hn kappa tau ring C es :=
  Local3EntryOrCap_physical_endpoint hpsi h2 hn kappa tau ring C es
    (twoCross_success_entry_or_cap
      hpsi h2 hn kappa tau ring C hline es hs)


/-- Indicator of the literal full-host `Local3EntryOrCap` event on one original
raw scheduler word.  `h2` supplies positivity of `psi`; there is no separate
mathematical premise. -/
noncomputable def actualEventBit
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (es : List (Fin n)) : Nat := by
  classical
  exact if Local3EntryOrCap (by omega : 0 < psi) h2 hn
    kappa tau ring C es then 1 else 0


/-- Exact numerator over all original length-T `Fin n` scheduler words. -/
noncomputable def actualEventCount
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (actualEventBit h2 hn kappa tau ring C)


private theorem stopped_word_sum {S : Type} {n : Nat}
    (next : S -> Fin n -> StopNode S) (wt : StopNode S -> Nat)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
        (fun es => wt (runWord next x es)) =
      treeWeight next wt x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules, runWord, treeWeight]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode next x e))


/-- Wordwise domination on the unchanged raw scheduler alphabet.  A stopped
matcher success may have any suffix; absorption plus the accepted producer
puts that entire word in the literal physical event. -/
theorem successWeight_le_actualEventBit
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (hline : LocalLine3 (by omega : 0 < psi) hn C)
    (es : List (Fin n)) :
    successWeight
        (runWord (twoCrossStep hn) (.active false) es) <=
      actualEventBit h2 hn kappa tau ring C es := by
  classical
  cases hx : runWord (twoCrossStep hn) (.active false) es with
  | active b =>
      simp [successWeight, actualEventBit, hx]
  | failure =>
      simp [successWeight, actualEventBit, hx]
  | success =>
      have he := twoCross_success_entry_or_cap
        (by omega : 0 < psi) h2 hn kappa tau ring C hline es hx
      simp [successWeight, actualEventBit, hx, he]


/-- Exact raw-word comparison: every stopped-tree success word is counted by
the literal full-host event numerator, with no conditioning or distribution
transfer. -/
theorem successCount_le_actualEventCount
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (hline : LocalLine3 (by omega : 0 < psi) hn C)
    (T : Nat) :
    successCount (twoCrossStep hn) (.active false) T <=
      actualEventCount h2 hn kappa tau ring C T := by
  unfold successCount actualEventCount
  rw [← stopped_word_sum (twoCrossStep hn) successWeight (.active false) T]
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => successWeight
        (runWord (twoCrossStep hn) (.active false) es)),
    ← FixedSpanRenewalPayload.rawWord_sum n T
      (actualEventBit h2 hn kappa tau ring C)]
  exact ofFn_sum_le _ _ (fun i =>
    successWeight_le_actualEventBit h2 hn kappa tau ring C hline
      (FixedSpanRenewalPayload.rawWord n T i))


/-- Literal original-word numerator at horizon `4*n`.


Hypotheses are exactly width availability `2 <= psi`, ring size `4 <= n`, and
`LocalLine3`; kappa, tau, and all metadata outside the local line remain
arbitrary. -/
theorem local3_entry_or_cap_sixteenth
    (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (hline : LocalLine3 (by omega : 0 < psi) hn C) :
    n^(4*n) <= 16 *
      actualEventCount h2 hn kappa tau ring C (4*n) := by
  have hm := two_cross_sixteenth hn
  have hp := successCount_le_actualEventCount
    h2 hn kappa tau ring C hline (4*n)
  exact Nat.le_trans hm (Nat.mul_le_mul_left 16 hp)


#print axioms BirthShortDoneTerminalPassiveLocal3Mass.Local3EntryOrCap_physical_endpoint
#print axioms BirthShortDoneTerminalPassiveLocal3Mass.twoCross_success_physical_endpoint
#print axioms BirthShortDoneTerminalPassiveLocal3Mass.successCount_le_actualEventCount
#print axioms BirthShortDoneTerminalPassiveLocal3Mass.local3_entry_or_cap_sixteenth


end BirthShortDoneTerminalPassiveLocal3Mass
