import Leader.AAFJ.PaperClean
import Leader.AAFJ.GlobalFairness
import Leader.AAFJ.OneBarrier.UniqueReachesClean
import Leader.AAFJ.MultiBarrier.ReachesOneBarrier

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPaper9Complete

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup
open PopulationProtocol.GlobalFairness

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e es ih =>
      simpa only [List.cons_append, rawRun] using
        ih ((protocol k hk).step ring C e)

private theorem all_false_of_bitCount_eq_zero
    {n : Nat} (bits : Fin n → Bool)
    (hcount : bitCount bits = 0) :
    ∀ i : Fin n, bits i = false := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      rw [bitCount_succ] at hcount
      cases hhead : bits 0 with
      | false =>
          have htailCount :
              bitCount (fun i : Fin n => bits i.succ) = 0 := by
            simpa [hhead] using hcount
          have htail :=
            ih (fun i : Fin n => bits i.succ) htailCount
          intro i
          exact Fin.cases hhead htail i
      | true =>
          simp [hhead] at hcount

private theorem exists_unique_true_of_bitCount_eq_one
    {n : Nat} (bits : Fin n → Bool)
    (hcount : bitCount bits = 1) :
    ∃ leader : Fin n,
      bits leader = true ∧
      ∀ i : Fin n, bits i = true → i = leader := by
  induction n with
  | zero =>
      simp [bitCount] at hcount
  | succ n ih =>
      rw [bitCount_succ] at hcount
      cases hhead : bits 0 with
      | false =>
          have htailCount :
              bitCount (fun i : Fin n => bits i.succ) = 1 := by
            simpa [hhead] using hcount
          obtain ⟨leader, hleader, honly⟩ :=
            ih (fun i : Fin n => bits i.succ) htailCount
          refine ⟨leader.succ, hleader, ?_⟩
          intro i hi
          exact Fin.cases
            (fun hzero => by simp [hhead] at hzero)
            (fun j hj => congrArg Fin.succ (honly j hj))
            i hi
      | true =>
          have htailCount :
              bitCount (fun i : Fin n => bits i.succ) = 0 := by
            have h := hcount
            simp [hhead] at h
            exact h
          have htailFalse :=
            all_false_of_bitCount_eq_zero
              (fun i : Fin n => bits i.succ) htailCount
          refine ⟨0, hhead, ?_⟩
          intro i hi
          exact Fin.cases
            (fun _ => rfl)
            (fun j hj => by
              have hf := htailFalse j
              rw [hf] at hj
              contradiction)
            i hi

private theorem oneBarrierAt_rawRun_exists
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hnd : ¬ k ∣ n) :
    ∀ w : List (Fin n),
      ∀ C : Fin n → State k,
        ∀ b : Fin n,
          OneBarrierAt hk ring C b →
            ∃ b' : Fin n,
              OneBarrierAt hk ring (rawRun hk ring C w) b' := by
  intro w
  induction w with
  | nil =>
      intro C b hB
      exact ⟨b, by simpa [rawRun] using hB⟩
  | cons e es ih =>
      intro C b hB
      let C₁ := (protocol k hk).step ring C e
      let b₁ :=
        if AdvanceReady hk ring C e then ring.rightNeighbor b else b
      have hB₁ : OneBarrierAt hk ring C₁ b₁ := by
        dsimp only [C₁, b₁]
        exact oneBarrierAt_step hk ring hn2 C b e hnd hB
      obtain ⟨b', hB'⟩ := ih C₁ b₁ hB₁
      refine ⟨b', ?_⟩
      simpa [rawRun, C₁] using hB'

/-- The complete one-barrier half of journal Lemma 9.2. -/
theorem oneBarrier_reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) :
    ∃ w : List (Fin n), Clean hk ring (rawRun hk ring C w) := by
  have hn2 : 1 < n := by omega
  obtain ⟨u, hu⟩ :=
    AAFJPK.OriginalOneBarrierReduce.reduce_leaders
      hk ring hn3 hnd C b hB
  let D := rawRun hk ring C u
  change
    OneBarrierAt hk ring D b ∧
      (leaderCount D ≤ 1 ∨
        ∃ p : Fin n,
          p ≠ ring.rightNeighbor b ∧
          (D p).leader = true ∧
          (D p).bullet = false ∧
          (D (ring.rightNeighbor b)).leader = true ∧
          ∀ i : Fin n,
            (D i).leader = true →
              i = p ∨ i = ring.rightNeighbor b) at hu
  rcases hu with ⟨hBD, hred⟩
  rcases hred with hsmall | hpair
  · have hcases :
        leaderCount D = 0 ∨ leaderCount D = 1 := by
      omega
    rcases hcases with hzero | hone
    · have hbits :
          bitCount (fun i : Fin n => (D i).leader) = 0 := by
        simpa [leaderCount] using hzero
      have h0 : ∀ i : Fin n, (D i).leader = false :=
        all_false_of_bitCount_eq_zero
          (fun i : Fin n => (D i).leader) hbits
      obtain ⟨v, hclean⟩ :=
        AAFJPK.OriginalOneBarrierLeaderless.leaderless_reaches_clean
          hk ring hn3 hnd D b hBD h0
      refine ⟨u ++ v, ?_⟩
      rw [rawRun_append hk ring C u v]
      simpa [D] using hclean
    · have hbits :
          bitCount (fun i : Fin n => (D i).leader) = 1 := by
        simpa [leaderCount] using hone
      obtain ⟨l, hl, honly⟩ :=
        exists_unique_true_of_bitCount_eq_one
          (fun i : Fin n => (D i).leader) hbits
      obtain ⟨v, hv⟩ :=
        AAFJPK.OriginalOneBarrierUnique.unique_reaches_clean_or_leaderless
          hk ring hn3 hnd D b hBD l hl honly
      rcases hv with hclean | hleaderless
      · refine ⟨u ++ v, ?_⟩
        rw [rawRun_append hk ring C u v]
        simpa [D] using hclean
      · obtain ⟨b', hB'⟩ :=
          oneBarrierAt_rawRun_exists
            hk ring hn2 hnd v D b hBD
        obtain ⟨z, hclean⟩ :=
          AAFJPK.OriginalOneBarrierLeaderless.leaderless_reaches_clean
            hk ring hn3 hnd
              (rawRun hk ring D v) b' hB' hleaderless
        refine ⟨u ++ (v ++ z), ?_⟩
        rw [rawRun_append hk ring C u (v ++ z)]
        rw [rawRun_append hk ring
          (rawRun hk ring C u) v z]
        simpa [D] using hclean
  · rcases hpair with
      ⟨p, hph, hp, _hbul, hh, honly⟩
    obtain ⟨v, hclean⟩ :=
      AAFJPK.OriginalOneBarrierHeadPair.headPair_reaches_clean
        hk ring hn3 hnd D b hBD p hph hp hh honly
    refine ⟨u ++ v, ?_⟩
    rw [rawRun_append hk ring C u v]
    simpa [D] using hclean

/-- Complete qualitative form of journal Lemma 9.2 for generalized P_k:
every configuration reaches Clean when k does not divide the ring size. -/
theorem reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) :
    ∃ D : Fin n → State k,
      PopulationProtocol.Reachable (protocol k hk) ring C D ∧
        Clean hk ring D := by
  obtain ⟨D, b, hCD, hB⟩ :=
    AAFJPK.OriginalQualitative.reaches_oneBarrierAt
      hk ring (by omega) hnd C
  obtain ⟨w, hclean⟩ :=
    oneBarrier_reaches_clean hk ring hn3 hnd D b hB
  refine ⟨rawRun hk ring D w, ?_, hclean⟩
  exact hCD.trans
    (AAFJPK.OriginalQualitative.rawRun_reachable
      hk ring D w)

/-- Journal Lemma 9.2 for odd rings and literal Protocol 6 (P_2). -/
theorem paperLemma9_2
    {n : Nat} (hodd : AAFJPaper9.OddRing n)
    (ring : DirectedRing n) (C : Fin n → AAFJPK.State 2) :
    ∃ D : Fin n → AAFJPK.State 2,
      PopulationProtocol.Reachable
          (AAFJPK.protocol 2 (by decide)) ring C D ∧
        AAFJPaper9.PaperClean (by decide) ring D := by
  obtain ⟨D, hCD, hclean⟩ :=
    reaches_clean
      (by decide) ring hodd.three_le hodd.not_two_dvd C
  refine ⟨D, hCD, ?_⟩
  exact
    (AAFJPaper9.paperClean_iff_clean
      (by decide) ring D).2 hclean

/-- Journal Theorem 9.4: for fixed k >= 2 and k not dividing n, every legal
globally fair execution stabilizes forever with one physical leader. -/
theorem paperTheorem9_4
    {n k : Nat} (hk2 : 2 ≤ k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hnd : ¬ k ∣ n)
    {exec : Nat → (Fin n → AAFJPK.State k)}
    (hexec :
      PopulationProtocol.GlobalFairness.GloballyFairExecution
        (AAFJPK.protocol k (by omega)) ring exec) :
    ∃ t : Nat, ∃ ell : Fin n,
      ∀ s : Nat, t ≤ s →
        CleanForLeader (by omega) ring ell (exec s) ∧
          PopulationProtocol.IsSafe
            (AAFJPK.protocol k (by omega)) ring
            (exec s) (fun bit => bit) := by
  have hreaches :
      ∀ state : Fin n → AAFJPK.State k,
        ∃ target : Fin n → AAFJPK.State k,
          PopulationProtocol.Reachable
              (AAFJPK.protocol k (by omega)) ring state target ∧
            Clean (by omega) ring target := by
    intro state
    exact reaches_clean (by omega) ring hn3 hnd state
  have hevent :
      PopulationProtocol.GlobalFairness.Eventually
        exec (Clean (by omega) ring) := by
    exact
      PopulationProtocol.GlobalFairness.eventually_of_globallyFair_reachable_closed
        (PopulationProtocol.GlobalFairness.configurationCertificate
          (AAFJPK.protocol k (by omega))
          (AAFJPK.states k) n)
        hexec
        hreaches
        (AAFJPK.SingleBarrierSanitation.clean_closed
          (by omega) ring hn3 hnd)
  obtain ⟨t, ht⟩ := hevent
  obtain ⟨ell, hcleanT⟩ := ht
  refine ⟨t, ell, ?_⟩
  intro s hts
  have hreach :
      PopulationProtocol.Reachable
        (AAFJPK.protocol k (by omega)) ring
        (exec t) (exec s) :=
    PopulationProtocol.GlobalFairness.reachable_of_abstract
      (FiniteTransitionSystem.reachable_of_time_le
        hexec.legal hts)
  have hcleanS :
      CleanForLeader (by omega) ring ell (exec s) :=
    AAFJPK.SingleBarrierSanitation.cleanForLeader_reachable
      (by omega) ring hn3 hnd ell hcleanT hreach
  exact
    ⟨hcleanS,
      AAFJPK.SingleBarrierSanitation.cleanForLeader_isSafe
        (by omega) ring hn3 hnd (exec s) ell hcleanS⟩

/-- Journal Theorem 9.3, obtained from Theorem 9.4 at k = 2 and translated
back to the paper's Clean predicate. -/
theorem paperTheorem9_3
    {n : Nat} (hodd : AAFJPaper9.OddRing n)
    (ring : DirectedRing n)
    {exec : Nat → (Fin n → AAFJPK.State 2)}
    (hexec :
      PopulationProtocol.GlobalFairness.GloballyFairExecution
        (AAFJPK.protocol 2 (by decide)) ring exec) :
    ∃ t : Nat, ∃ ell : Fin n,
      ∀ s : Nat, t ≤ s →
        AAFJPaper9.PaperCleanForLeader
            (by decide) ring ell (exec s) ∧
          PopulationProtocol.IsSafe
            (AAFJPK.protocol 2 (by decide)) ring
            (exec s) (fun bit => bit) := by
  have hexec' :
      PopulationProtocol.GlobalFairness.GloballyFairExecution
        (AAFJPK.protocol 2 (by omega)) ring exec := by
    simpa using hexec
  obtain ⟨t, ell, hstable⟩ :=
    paperTheorem9_4
      (n := n) (k := 2) (by decide)
      ring hodd.three_le hodd.not_two_dvd hexec'
  refine ⟨t, ell, ?_⟩
  intro s hts
  have hs := hstable s hts
  refine ⟨?_, ?_⟩
  · exact
      (AAFJPaper9.paperCleanForLeader_iff_cleanForLeader
        (by decide) ring ell (exec s)).2
        (by simpa using hs.1)
  · simpa using hs.2

#print axioms oneBarrier_reaches_clean
#print axioms reaches_clean
#print axioms paperLemma9_2
#print axioms paperTheorem9_4
#print axioms paperTheorem9_3

end AAFJPaper9Complete
