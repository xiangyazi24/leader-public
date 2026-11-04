import Leader.L3.Top.ClockBundle
import Leader.L3.Top.FreshTailEntrancePreimage
import Leader.L3.Top.FreshTailEntranceAccept

/-!
# The first-genuine entrance, proved

Lemma S of the paper entrance has two halves: the accept predecessor
(`topFreshTailEntranceAcceptPredecessor`: the last letter of the word is the
terminal service that exports the genuine tail) and the sample preimage
(`topFreshTailEntranceSamplePreimage`: the sample has a historical source-zero
U service).  This module joins them into the factorization that
`topFreshTailEntranceOfFactorization` consumes, which proves
`TopFreshTailFirstGenuineEntrance` and hence the old Q9 request clock.
-/

namespace L3

/-- Every list is empty or ends in a last letter.
Consumer: `topFreshTailFirstGenuineEntranceProved`. -/
private theorem listNilOrSnoc {α : Type} (l : List α) :
    l = [] ∨ ∃ (L : List α) (b : α), l = L ++ [b] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a t ih =>
      right
      rcases ih with rfl | ⟨L, b, rfl⟩
      · exact ⟨[], a, rfl⟩
      · exact ⟨a :: L, b, rfl⟩

/-- The first-genuine entrance of the post-anchor cohort wave.
Consumer: `stageRequestMissingClockProved`. -/
theorem topFreshTailFirstGenuineEntranceProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    TopFreshTailFirstGenuineEntrance ring hn := by
  intro C s hl hbad Z hpre haccepted
  obtain ⟨word, e, P, sigma, exported, hw, he, hP, _, hrec, _, hlane, hsite,
    _, _, _, _, _, _, _, _, _, hdata, hatom, hyi, hyc⟩ :=
    topFreshTailEntranceAcceptPredecessor ring C s Z hpre haccepted
  have hreach : Z = topFixedTraceRun ring C Z.2 := hpre.1
  obtain ⟨u, tail, hsplit, hunread, hstamp⟩ :=
    topFreshTailEntranceSamplePreimage ring C s Z Z.2 hreach sigma hrec hlane hsite
  have hr : 3 ≤ topClockSpan n := cert_rho_ge_three n hn
  subst he
  subst hP
  have h := hw.symm.trans hsplit
  rcases listNilOrSnoc tail with rfl | ⟨v, y, rfl⟩
  · exfalso
    rw [List.append_nil] at h
    have hsingle := (List.append_inj' h rfl).2
    have hes : certSite s (topClockSpan n - 1) = certSite s 0 := by
      injection hsingle
    have hinj := topFreshTailCausalSourceSiteInjective s hn
      (⟨topClockSpan n - 1, by omega⟩ : Fin (topClockSpan n))
      (⟨0, by omega⟩ : Fin (topClockSpan n)) hes
    have hv : topClockSpan n - 1 = 0 := congrArg Fin.val hinj
    omega
  · rw [← List.append_assoc] at h
    obtain ⟨hwd, _⟩ := List.append_inj' h rfl
    subst hwd
    exact topFreshTailEntranceOfFactorization ring C s hn hbad hl Z hpre haccepted
      u v sigma hw hunread hlane hsite hstamp hdata hatom hyi hyc

/-- The old Q9 request clock, with no premise beyond `5 ≤ n`.
Consumer: `l3HeadlineOfCleanBranches` (HeadlineCleanAssembly). -/
theorem stageRequestMissingClockProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageRequestMissingClock ring :=
  stageRequestMissingClockOfEntrance ring hn
    (topFreshTailFirstGenuineEntranceProved ring hn)

end L3

#print axioms L3.topFreshTailFirstGenuineEntranceProved
#print axioms L3.stageRequestMissingClockProved
