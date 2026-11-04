import Leader.L3.Small.FinishClean

/-!
SMALL clean reader: causal E.G19 retirement on the *actual* renewalSmallNext
scheduler, and the source-independent E.G22 initial and run lemmas.

The E.G19 cost is t*n^2, where t = smallRepairWidth n =
(compileAdvice (ceilLogTwo n)).t.  No identification of t with
ceilLogTwo (ceilLogTwo n) is made.

The unrestricted SMALL E.G22 numerical owner-step and the R0c
root-window terminal comparison are not claimed here: installed
BANK lemmas at those points require useSmall=false.
-/

namespace L3.SmallReaderClean

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallFinishRepair
open L3.SmallRepairStages
open L3.SmallFinishClean
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! E.G19: the causal reader-control trace on the SMALL reference. -/

/-- The physical SMALL state paired with its actual causal R controller.
Consumer: smallCleanReaderCoupledNext and smallCleanReaderTrace. -/
abbrev SmallCleanReaderCoupledState (n : Nat) :=
  RenewalSmallReference n ×
    BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))

/-- One actual masked SMALL edge, followed by the genuine R observer.
Consumer: smallCleanReaderTraceSnoc and the E.G19 Bellman drift. -/
noncomputable def smallCleanReaderCoupledNext {n : Nat}
    (ring : DirectedRing n)
    (z : SmallCleanReaderCoupledState n) (e : Fin n) :
    SmallCleanReaderCoupledState n :=
  (renewalSmallNext ring z.1 e,
    BlockA.readerControlNext ring z.2 (piR z.1.1) e
      (piR (renewalSmallNext ring z.1 e).1))

/-- An actual physical scheduler word, not an independent phiR chain.
Consumer: smallCleanReaderTraceFacts. -/
noncomputable def smallCleanReaderTrace {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n)
    (word : List (Fin n)) : SmallCleanReaderCoupledState n :=
  word.foldl (smallCleanReaderCoupledNext ring)
    (start, smallRepairReaderInitialControl ring start)

/-- The requested literal trace-snoc identity.
Consumer: smallCleanReaderTraceFacts and smallCleanReaderWordDrift. -/
theorem smallCleanReaderTraceSnoc {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n)
    (word : List (Fin n)) (e : Fin n) :
    smallCleanReaderTrace ring start (word ++ [e]) =
      smallCleanReaderCoupledNext ring
        (smallCleanReaderTrace ring start word) e := by
  unfold smallCleanReaderTrace
  rw [List.foldl_append]
  rfl

/-- The physical projection of a paired fold is the original SMALL fold.
Consumer: smallCleanReaderTracePhysical. -/
private theorem smallCleanReaderCoupledPhysicalFold {n : Nat}
    (ring : DirectedRing n)
    (z : SmallCleanReaderCoupledState n) (word : List (Fin n)) :
    (word.foldl (smallCleanReaderCoupledNext ring) z).1 =
      word.foldl (renewalSmallNext ring) z.1 := by
  induction word generalizing z with
  | nil => rfl
  | cons e tail ih =>
      change
        (tail.foldl (smallCleanReaderCoupledNext ring)
          (smallCleanReaderCoupledNext ring z e)).1 =
        tail.foldl (renewalSmallNext ring)
          (renewalSmallNext ring z.1 e)
      exact ih _

/-- The coupled trace has no alternative physical transition.
Consumer: smallCleanReaderDoneCertifies and cost comparison. -/
theorem smallCleanReaderTracePhysical {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n)
    (word : List (Fin n)) :
    (smallCleanReaderTrace ring start word).1 =
      word.foldl (renewalSmallNext ring) start := by
  unfold smallCleanReaderTrace
  exact smallCleanReaderCoupledPhysicalFold ring
    (start, smallRepairReaderInitialControl ring start) word

/-- The canonical SMALL initializer satisfies the E.G19 tag support
invariant, without BANK width or band assumptions.
Consumer: smallCleanReaderTraceFacts. -/
theorem smallCleanReaderTaggedInitial {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n) :
    BankRepairCloseReaderTagged (piR start.1)
      (smallRepairReaderInitialControl ring start) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i name hi
    by_cases hs : (piR start.1 i).rawTok.isSome = true
    · exact hs
    · simp [smallRepairReaderInitialControl, hs] at hi
  · intro name
    constructor
    · intro hname
      refine ⟨name, ?_⟩
      have hs : (piR start.1 name).rawTok.isSome = true := hname
      simp [smallRepairReaderInitialControl, hs]
    · rintro ⟨i, hi⟩
      by_cases hs : (piR start.1 i).rawTok.isSome = true
      · simp [smallRepairReaderInitialControl, hs] at hi
        rw [← hi]
        exact hs
      · simp [smallRepairReaderInitialControl, hs] at hi
  · intro hdone
    cases hdone

/-- The joint SAME-word SMALL coupling: every prefix retains the
grant-free guard, the inherited-name tag invariant, and a genuine
BlockA.Run of phiR. Consumer: E.G19 potential and done certificate. -/
theorem smallCleanReaderTraceFacts {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (start : RenewalSmallReference n)
    (hguard : SmallRepairGuard ring start) :
    ∀ word : List (Fin n),
      SmallRepairGuard ring
        (smallCleanReaderTrace ring start word).1 ∧
      BankRepairCloseReaderTagged
        (piR (smallCleanReaderTrace ring start word).1.1)
        (smallCleanReaderTrace ring start word).2 ∧
      BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
        (piR start.1)
        (.live (piR start.1)
          (smallRepairReaderInitialControl ring start))
        word
        (piR (smallCleanReaderTrace ring start word).1.1)
        (.live (piR (smallCleanReaderTrace ring start word).1.1)
          (smallCleanReaderTrace ring start word).2) := by
  intro word
  suffices hk : ∀ (k : Nat) (w : List (Fin n)), w.length = k →
      SmallRepairGuard ring
        (smallCleanReaderTrace ring start w).1 ∧
      BankRepairCloseReaderTagged
        (piR (smallCleanReaderTrace ring start w).1.1)
        (smallCleanReaderTrace ring start w).2 ∧
      BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
        (piR start.1)
        (.live (piR start.1)
          (smallRepairReaderInitialControl ring start))
        w
        (piR (smallCleanReaderTrace ring start w).1.1)
        (.live (piR (smallCleanReaderTrace ring start w).1.1)
          (smallCleanReaderTrace ring start w).2) from
    hk word.length word rfl
  intro k
  induction k with
  | zero =>
      intro w hw
      have hnil : w = [] := List.eq_nil_of_length_eq_zero hw
      subst hnil
      exact ⟨hguard, smallCleanReaderTaggedInitial ring start,
        BlockA.Run.empty⟩
  | succ k ih =>
      intro w hw
      rcases List.eq_nil_or_concat w with hnil | ⟨w', b, hcat⟩
      · subst hnil
        simp at hw
      · rw [List.concat_eq_append] at hcat
        subst hcat
        have hlen : w'.length = k := by
          simp at hw
          omega
        obtain ⟨hg, htag, hrun⟩ := ih w' hlen
        rw [smallCleanReaderTraceSnoc]
        have hphi := smallRepairReaderPhiStep ring
          (by omega : 2 ≤ n)
          (smallCleanReaderTrace ring start w').1 hg b
        refine ⟨?_, ?_, ?_⟩
        · exact smallRepairGuardStep ring hn hsmall
            (smallCleanReaderTrace ring start w').1 hg b
        · change BankRepairCloseReaderTagged
            (piR (renewalSmallNext ring
              (smallCleanReaderTrace ring start w').1 b).1)
            (BlockA.readerControlNext ring
              (smallCleanReaderTrace ring start w').2
              (piR (smallCleanReaderTrace ring start w').1.1) b
              (piR (renewalSmallNext ring
                (smallCleanReaderTrace ring start w').1 b).1))
          rw [hphi]
          exact bankRepairCloseTaggedStep ring (by omega : 2 ≤ n)
            _ _ _ b htag
        · change BlockA.Run ring (phiR ring)
            (BlockA.readerControlNext ring)
            (piR start.1)
            (.live (piR start.1)
              (smallRepairReaderInitialControl ring start))
            (w' ++ [b])
            (piR (renewalSmallNext ring
              (smallCleanReaderTrace ring start w').1 b).1)
            (.live (piR (renewalSmallNext ring
                (smallCleanReaderTrace ring start w').1 b).1)
              (BlockA.readerControlNext ring
                (smallCleanReaderTrace ring start w').2
                (piR (smallCleanReaderTrace ring start w').1.1) b
                (piR (renewalSmallNext ring
                  (smallCleanReaderTrace ring start w').1 b).1)))
          rw [hphi]
          have hs := BlockA.Run.next hrun b
          simpa [BlockA.update] using hs

/-- The terminal bit on this specific coupled SMALL trace.
Consumer: smallCleanReaderDoneCertifies. -/
noncomputable def smallCleanReaderWordDone {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n)
    (word : List (Fin n)) : Prop :=
  (smallCleanReaderTrace ring start word).2.phase = .done

/-- Corrected inherited-reader debt, including the final one-edge
ticket when the last name has vanished. Consumer: E.G19 Bellman cost. -/
noncomputable def smallCleanReaderWordDebt {n : Nat}
    (ring : DirectedRing n) (start : RenewalSmallReference n)
    (word : List (Fin n)) : Nat :=
  bankRepairReaderResidentPotential
    (piR (smallCleanReaderTrace ring start word).1.1)
    (smallCleanReaderTrace ring start word).2

/-- A done causal SMALL trace implies no inherited names and
certifies the SAME-fold CleanWord-origin retirement target.
Consumer: smallCleanReaderWordCostLe. -/
theorem smallCleanReaderDoneCertifies {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (start : RenewalSmallReference n)
    (hw : SmallCleanWAcceptedOnGuard ring start)
    (word : List (Fin n))
    (hdone : smallCleanReaderWordDone ring start word) :
    SmallCleanReaderRetiredFrom ring start
      (word.foldl (renewalSmallNext ring) start) := by
  obtain ⟨_, htag, hrun⟩ :=
    smallCleanReaderTraceFacts ring hn hsmall start hw.1 word
  have hphysical := smallCleanReaderTracePhysical ring start word
  rw [hphysical] at hrun
  have hd : (smallCleanReaderTrace ring start word).2.phase = .done :=
    hdone
  have hnames : ∀ name : Fin n,
      (smallCleanReaderTrace ring start word).2.inheritedNames
        name = false := by
    intro name
    cases hb : (smallCleanReaderTrace ring start word).2.inheritedNames
        name with
    | false => rfl
    | true =>
        obtain ⟨i, hi⟩ := (htag.2.1 name).1 hb
        exact absurd hi (htag.2.2 hd i name)
  exact ⟨word,
    .live (piR start.1)
      (smallRepairReaderInitialControl ring start),
    (smallCleanReaderTrace ring start word).2,
    rfl,
    smallCleanReaderInitializesAtWord ring start hw.2,
    hrun, hd, hnames⟩

/-- Bellman drift of the actual SMALL resident trace, directly using
the c-generic BANK R0/R1 row lemma. No BANK width identity occurs.
Consumer: smallCleanResidentRetirementClockProved. -/
theorem smallCleanReaderWordDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (start : RenewalSmallReference n)
    (hg : SmallRepairGuard ring start)
    (word : List (Fin n))
    (hnot : ¬ smallCleanReaderWordDone ring start word) :
    1 + (List.ofFn (fun e : Fin n =>
      smallCleanReaderWordDebt ring start (word ++ [e]))).sum ≤
      n * smallCleanReaderWordDebt ring start word := by
  obtain ⟨hgword, htag, _⟩ :=
    smallCleanReaderTraceFacts ring hn hsmall start hg word
  have hsum :
      (List.ofFn (fun e : Fin n =>
        smallCleanReaderWordDebt ring start (word ++ [e]))) =
      List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentPotential
          (phiR ring
            (piR (smallCleanReaderTrace ring start word).1.1) e)
          (BlockA.readerControlNext ring
            (smallCleanReaderTrace ring start word).2
            (piR (smallCleanReaderTrace ring start word).1.1) e
            (piR (renewalSmallNext ring
              (smallCleanReaderTrace ring start word).1 e).1))) := by
    congr 1
    funext e
    unfold smallCleanReaderWordDebt
    rw [smallCleanReaderTraceSnoc]
    have hphi := smallRepairReaderPhiStep ring (by omega : 2 ≤ n)
      (smallCleanReaderTrace ring start word).1 hgword e
    change bankRepairReaderResidentPotential
        (piR (renewalSmallNext ring
          (smallCleanReaderTrace ring start word).1 e).1)
        (BlockA.readerControlNext ring
          (smallCleanReaderTrace ring start word).2
          (piR (smallCleanReaderTrace ring start word).1.1) e
          (piR (renewalSmallNext ring
            (smallCleanReaderTrace ring start word).1 e).1)) = _
    rw [hphi]
  rw [hsum]
  exact bankRepairCloseDrift ring (by omega : 2 ≤ n) _ _
    (fun e => piR (renewalSmallNext ring
      (smallCleanReaderTrace ring start word).1 e).1)
    htag hnot

/-- A general tape-to-physical cost comparison: the causal SMALL
done predicate has a real retired-from witness at the same fold.
Consumer: smallCleanResidentRetirementClockProved. -/
theorem smallCleanReaderWordCostLe {n : Nat}
    (ring : DirectedRing n)
    (start : RenewalSmallReference n)
    (Q : List (Fin n) → Prop)
    (hQP : ∀ word : List (Fin n), Q word →
      SmallCleanReaderRetiredFrom ring start
        (word.foldl (renewalSmallNext ring) start))
    (word : List (Fin n)) (T : Nat) :
    costNumerator (renewalSmallNext ring)
      (SmallCleanReaderRetiredFrom ring start)
      (word.foldl (renewalSmallNext ring) start) T ≤
    costNumerator
      (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
      Q word T := by
  classical
  induction T generalizing word with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hp : SmallCleanReaderRetiredFrom ring start
          (word.foldl (renewalSmallNext ring) start)
      · rw [costNumerator_terminal
          (renewalSmallNext ring)
          (SmallCleanReaderRetiredFrom ring start)
          (word.foldl (renewalSmallNext ring) start)
          hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q word := by
          intro h
          exact hp (hQP word h)
        rw [costNumerator_succ
          (renewalSmallNext ring)
          (SmallCleanReaderRetiredFrom ring start)
          (word.foldl (renewalSmallNext ring) start)
          hp T]
        rw [costNumerator_succ
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          Q word hq T]
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (renewalSmallNext ring)
              (SmallCleanReaderRetiredFrom ring start)
              (renewalSmallNext ring
                (word.foldl (renewalSmallNext ring) start) e) T)
          (fun e : Fin n =>
            costNumerator
              (fun (w : List (Fin n)) (f : Fin n) => w ++ [f])
              Q (word ++ [e]) T)
          (fun e => by
            have h := ih (word ++ [e])
            simpa only [List.foldl_append, List.foldl_cons,
              List.foldl_nil] using h)
        exact Nat.add_le_add_left hsum (n ^ (T + 1))

/-- The SMALL clean E.G19 retirement clock: no hypothesis beyond the
SMALL band, ring size, and the actually proved grant-free guard.
The cap is n*t, never n*psi.
Consumer: SmallFinishClean.smallCleanReaderHalfStageOfRetirementAndFold. -/
theorem smallCleanResidentRetirementClockProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallCleanResidentRetirementClock ring := by
  intro start hw T
  have hdrift : ∀ word : List (Fin n),
      ¬ smallCleanReaderWordDone ring start word →
      1 + (List.ofFn (fun e : Fin n =>
        smallCleanReaderWordDebt ring start (word ++ [e]))).sum ≤
        n * smallCleanReaderWordDebt ring start word := by
    intro word hnot
    exact smallCleanReaderWordDrift ring hn hsmall start hw.1 word hnot
  have hscaled :
      ∀ word : List (Fin n),
        ¬ smallCleanReaderWordDone ring start word →
        n + (List.ofFn (fun e : Fin n =>
          n * smallCleanReaderWordDebt ring start (word ++ [e]))).sum ≤
        n * (n * smallCleanReaderWordDebt ring start word) := by
    intro word hnot
    have hbase := hdrift word hnot
    have hm := Nat.mul_le_mul_left n hbase
    calc
      n + (List.ofFn (fun e : Fin n =>
        n * smallCleanReaderWordDebt ring start (word ++ [e]))).sum =
        n * (1 + (List.ofFn (fun e : Fin n =>
          smallCleanReaderWordDebt ring start (word ++ [e]))).sum) := by
          simp only [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      _ ≤ n * (n * smallCleanReaderWordDebt ring start word) := hm
  have hword := Prob.costNumerator_le_of_potential
    (fun (word : List (Fin n)) (e : Fin n) => word ++ [e])
    (smallCleanReaderWordDone ring start)
    (fun word => n * smallCleanReaderWordDebt ring start word)
    hscaled
  have hcap :
      smallCleanReaderWordDebt ring start [] ≤
        n * smallRepairWidth n := by
    have hc := bankRepairReaderResidentPotentialCap
      (piR start.1)
      (smallRepairReaderInitialControl ring start)
      ring.hn (ClosureFull.adviceWidthPositive (ceilLogTwo n))
    change smallCleanReaderWordDebt ring start [] ≤
      n * (compileAdvice (ceilLogTwo n)).t at hc
    exact hc
  have hbound :
      n * smallCleanReaderWordDebt ring start [] ≤
        smallRepairWidth n * n ^ 2 := by
    calc
      n * smallCleanReaderWordDebt ring start [] ≤
        n * (n * smallRepairWidth n) :=
          Nat.mul_le_mul_left n hcap
      _ = smallRepairWidth n * n ^ 2 := by
        rw [Nat.pow_two]
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hphysical := smallCleanReaderWordCostLe ring start
    (smallCleanReaderWordDone ring start)
    (fun word hdone =>
      smallCleanReaderDoneCertifies ring hn hsmall start hw word hdone)
    [] T
  have hcost :
      costNumerator (renewalSmallNext ring)
        (SmallCleanReaderRetiredFrom ring start) start T ≤
      n ^ T * (smallRepairWidth n * n ^ 2) := by
    calc
      costNumerator (renewalSmallNext ring)
          (SmallCleanReaderRetiredFrom ring start) start T ≤
        costNumerator
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          (smallCleanReaderWordDone ring start) [] T := hphysical
      _ ≤ n ^ T * (n * smallCleanReaderWordDebt ring start []) :=
        hword [] T
      _ ≤ n ^ T * (smallRepairWidth n * n ^ 2) :=
        Nat.mul_le_mul_left (n ^ T) hbound
  have hdouble := Nat.mul_le_mul_left 2 hcost
  calc
    2 * costNumerator (renewalSmallNext ring)
        (SmallCleanReaderRetiredFrom ring start) start T ≤
      2 * (n ^ T * (smallRepairWidth n * n ^ 2)) := hdouble
    _ = n ^ T * ((2 * smallRepairWidth n) * n ^ 2) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-! E.G22: the type-independent part that does not use a BANK band. -/

/-- E.G20, the genuine clean R initializer has a well-formed ghost
and no initial fresh ledger, at the SMALL t.
Consumer: a SMALL E.G22 numerical-run induction. -/
theorem smallCleanReaderNumericalOrigin {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader (CleanWord ring) p initial) :
    ∃ h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      initial = .live p h ∧ BankRepairReaderE22NumericalOnly p h := by
  obtain ⟨_, h, heq, hphase, hslots⟩ := hinit
  refine ⟨h, heq, ?_⟩
  constructor
  · exact Closure.readerGhostWellFormedStart p h hphase hslots
  · intro site name index samples htag
    exact False.elim
      ((bankRepairReaderE22InitialNoFresh p h hslots)
        site name index samples htag)

/-- The E.G22 numerical invariant propagates along a real decorated
SMALL phiR Run provided the (currently BANK-band-restricted) local
R0/R1 numerical owner row has been generalized to the SMALL t.
Consumer: the clean reader sample-window invariant. -/
theorem smallCleanReaderNumericalRunOfOwnerStep {n : Nat}
    (ring : DirectedRing n)
    (hstep :
      ∀ (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
        (h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
        (e : Fin n),
        BankRepairReaderE22NumericalOnly p h →
        BankRepairReaderE22NumericalOnly
          (phiR ring p e)
          (BlockA.readerControlNext ring h p e (phiR ring p e)))
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader (CleanWord ring) origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (gamma : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p gamma) :
    ∃ h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      gamma = .live p h ∧ BankRepairReaderE22NumericalOnly p h := by
  induction hrun with
  | empty =>
      exact smallCleanReaderNumericalOrigin ring origin initial hinit
  | @next w q gamma' hrunPrefix e ih =>
      obtain ⟨h, hgamma, hnumeric⟩ := ih
      refine ⟨BlockA.readerControlNext ring h q e
        (phiR ring q e), ?_, ?_⟩
      · rw [hgamma]
        classical
        simp [BlockA.update]
      · exact hstep q h e hnumeric

/-- E.G22 fixed-root transport along every genuine decorated SMALL
reader Run; no BANK width or numerical-sample assumption is used.
Consumer: the clean reader root-window proof. -/
theorem smallCleanReaderFixedRootAlongRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hfix : WFixedRoot ring root
      (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (gamma : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p gamma) :
    WFixedRoot ring root (AcceptedReceipts.wordProjectionR p) :=
  bankRepairCloseFixedRootAlongRun ring (by omega : 3 ≤ n)
    root origin initial hfix word p gamma hrun

end L3.SmallReaderClean

#print axioms L3.SmallReaderClean.smallCleanReaderTraceSnoc
#print axioms L3.SmallReaderClean.smallCleanReaderTracePhysical
#print axioms L3.SmallReaderClean.smallCleanReaderTaggedInitial
#print axioms L3.SmallReaderClean.smallCleanReaderTraceFacts
#print axioms L3.SmallReaderClean.smallCleanReaderDoneCertifies
#print axioms L3.SmallReaderClean.smallCleanReaderWordDrift
#print axioms L3.SmallReaderClean.smallCleanReaderWordCostLe
#print axioms L3.SmallReaderClean.smallCleanResidentRetirementClockProved
#print axioms L3.SmallReaderClean.smallCleanReaderNumericalOrigin
#print axioms L3.SmallReaderClean.smallCleanReaderNumericalRunOfOwnerStep
#print axioms L3.SmallReaderClean.smallCleanReaderFixedRootAlongRun
