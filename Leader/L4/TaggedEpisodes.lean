import Leader.L4.TaggedGeometry

namespace L4.TaggedTrace

/-- P3 makes its responder a nonleader and clears this incoming marker
before the birth guard. In particular no birth can undo the loss of that
responder's old leadership on the same mark. -/
theorem geometricPay_responder_nonleader {p c1 : Nat} (u v : Site p c1)
    (h : geometricPay u v = true) : (pairStep u v).2.leader = false := by
  have hp := (pair_geometric_fields u v).2.2
  simp only [h, if_true] at hp
  exact hp.2

private theorem ep_succ_inj {n : Nat} {i j : Fin n}
    (h : rightNeighbor i = rightNeighbor j) : i = j := by
  have hh := congrArg Fin.val h
  change (i.val + 1) % n = (j.val + 1) % n at hh
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hil : i.val + 1 < n <;> by_cases hjl : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hil, Nat.mod_eq_of_lt hjl] at hh
    omega
  · have hje : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hil, hje, Nat.mod_self] at hh
    omega
  · have hie : i.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hjl, hie, Nat.mod_self] at hh
    omega
  · omega

private theorem ep_succ_ne {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    rightNeighbor i ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  change (i.val + 1) % n = i.val at hh
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hh
    omega
  · have he : i.val + 1 = n := by omega
    rw [he,Nat.mod_self] at hh
    omega

/-- A long gap stays long for one step as long as its home is still a
leader at that same site. Under cover only P3 could insert a new mark.
Insertion at home would make it a nonleader; insertion farther inside
would require a payer on one of the old unmarked edges. -/
theorem isLong_step_of_surviving_leader {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (cover : MCOV x) (e z : Fin n)
    (hlong : TaggedFront.isLong x z = true)
    (hl : (step x e z).leader = true) :
    TaggedFront.isLong (step x e) z = true := by
  have hm : (x z).mark = false ∧ (x (rightNeighbor z)).mark = false ∧
      (x (rightNeighbor (rightNeighbor z))).mark = false := by
    simpa [TaggedFront.isLong, Bool.and_eq_true, and_assoc] using hlong
  have hnew (i : Fin n) (hi : (x i).mark = false)
      (hbad : geometricPay (x e) (x (rightNeighbor e)) = true →
        i ≠ rightNeighbor e) : (step x e i).mark = false := by
    rw [covered_step_mark hn x cover e i]
    by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
    · simp [hp,hbad hp,hi]
    · simp [hp,hi]
  have hhome : (step x e z).mark = false := by
    apply hnew z hm.1
    intro hp hz
    have hp' := geometricPay_responder_nonleader _ _ hp
    have hr : (step x e z).leader = false := by
      rw [hz]
      simp [step,ep_succ_ne hn e,hp']
    rw [hl] at hr
    contradiction
  have hinterior (i : Fin n) (hi : (x i).mark = false)
      (hin : (x (rightNeighbor i)).mark = false) :
      (step x e (rightNeighbor i)).mark = false := by
    apply hnew _ hin
    intro hp hj
    have hmarks := covered_pair_marks (x e) (x (rightNeighbor e)) (cover e)
    simp only [hp, if_true] at hmarks
    have he := ep_succ_inj hj
    rw [he, hmarks.1] at hi
    contradiction
  have h1 := hinterior z hm.1 hm.2.1
  have h2 := hinterior (rightNeighbor z) hm.2.1 hm.2.2
  simp [TaggedFront.isLong,hhome,h1,h2]

/-- Metadata required to charge at most one episode per observed living
tenure. The extra unit reserves the current tenure's budget until its
first long queue starts. -/
def EpisodeAccount {p c1 n : Nat} (s : Obs p c1 n) : Prop :=
  s.episodes + (s.priorLeader.isSome && s.priorQueue.isNone).toNat ≤ s.tenureCount

def EpisodeMemory {p c1 n : Nat} (s : Obs p c1 n) : Prop :=
  ∀ z q, s.priorQueue = some (z,q) →
    s.priorLeader = some z ∧
    (leaderNow s = some z → TaggedFront.isLong s.config z = true)

private theorem activeQueue_key {p c1 n : Nat} (s : Obs p c1 n) :
    (activeQueue s).map Prod.fst = (leaderNow s).filter (TaggedFront.isLong s.config) := by
  unfold activeQueue
  cases (leaderNow s).filter (TaggedFront.isLong s.config) <;> rfl

private theorem account_arithmetic {n : Nat}
    (a b : Nat) (lo ln qo qn : Option (Fin n))
    (oldOK : qo.isSome = true → qo = lo)
    (newOK : qn.isSome = true → qn = ln)
    (cont : qo.isSome = true → ln = lo → qn = qo)
    (h : a + (lo.isSome && qo.isNone).toNat ≤ b) :
    a + (qn.isSome && qn != qo).toNat + (ln.isSome && qn.isNone).toNat ≤
      b + (ln.isSome && ln != lo).toNat := by
  cases qn with
  | none =>
    cases ln with
    | none => simp_all [bne] <;> omega
    | some i =>
      cases lo with
      | none => simp_all [bne] <;> omega
      | some j =>
        by_cases he : i = j
        · subst i
          cases qo <;> simp_all [bne] <;> omega
        · cases qo <;> simp_all [bne] <;> try omega
          rw [show (i == j) = false from Bool.eq_false_iff.mpr
            (fun h => he (beq_iff_eq.mp h))]
          simp
          omega
  | some i =>
    have hn : ln = some i := (newOK rfl).symm
    subst ln
    cases qo with
    | none =>
      cases lo with
      | none => simp_all [bne] <;> omega
      | some j =>
        by_cases he : i = j
        · subst i; simp_all [bne] <;> omega
        · simp_all [bne] <;> omega
    | some j =>
      have ho : lo = some j := (oldOK rfl).symm
      subst lo
      simp_all [bne] <;> omega

/-- One accounting step conditional on consistent previous queue metadata. -/
theorem episodeAccount_step {p c1 n : Nat} {s : Obs p c1 n}
    (e : Fin n) (h : EpisodeAccount s) (hm : EpisodeMemory s) :
    EpisodeAccount (advance s e) := by
  cases hc : s.carrier with
  | none => simpa [EpisodeAccount,advance,hc] using h
  | some i =>
    have hk := activeQueue_key s
    have ho : (s.priorQueue.map Prod.fst).isSome = true →
        s.priorQueue.map Prod.fst = s.priorLeader := by
      cases hq : s.priorQueue with
      | none => simp
      | some a =>
        rcases a with ⟨z,q⟩
        simpa using (hm z q hq).1.symm
    have hn : ((activeQueue s).map Prod.fst).isSome = true →
        (activeQueue s).map Prod.fst = leaderNow s := by
      rw [hk]
      cases leaderNow s with
      | none => simp
      | some z => by_cases hz : TaggedFront.isLong s.config z = true <;>
          simp [Option.filter,hz]
    have hf : (s.priorQueue.map Prod.fst).isSome = true →
        leaderNow s = s.priorLeader →
        (activeQueue s).map Prod.fst = s.priorQueue.map Prod.fst := by
      cases hq : s.priorQueue with
      | none => simp
      | some a =>
        rcases a with ⟨z,q⟩
        obtain ⟨hz,hL⟩ := hm z q hq
        intro _ h
        have hh := h.trans hz
        simp [hk,hh, Option.filter, hL hh]
    have h' := account_arithmetic s.episodes s.tenureCount s.priorLeader (leaderNow s)
      (s.priorQueue.map Prod.fst) ((activeQueue s).map Prod.fst) ho hn hf
      (by simpa [EpisodeAccount] using h)
    simpa [EpisodeAccount, advance,hc,Option.map_map,Function.comp_def] using h'

private theorem leaderNow_live {p c1 n : Nat} {s : Obs p c1 n} {z : Fin n}
    (h : leaderNow s = some z) : (s.config z).leader = true := by
  cases hcar : s.carrier with
  | none => simp [leaderNow,hcar] at h
  | some i =>
    cases hr : TaggedFront.firstRoot s.config i with
    | none => simp [leaderNow,hcar,TaggedFront.firstLeader,hr] at h
    | some j =>
      by_cases hl : (s.config j).leader = true
      · have hj : j = z := by
          simpa [leaderNow,hcar,TaggedFront.firstLeader,hr,Option.filter,hl] using h
        simpa [hj] using hl
      · simp [leaderNow,hcar,TaggedFront.firstLeader,hr,Option.filter,hl] at h

private theorem episodeMemory_step {p c1 n : Nat} (hn : 4 ≤ n)
    (s : Obs p c1 n) (cov : MCOV s.config) (e : Fin n) (h : EpisodeMemory s) :
    EpisodeMemory (advance s e) := by
  intro z q hq
  cases hc : s.carrier with
  | none =>
    have hprev : s.priorQueue = some (z,q) := by simpa [advance,hc] using hq
    refine ⟨?_, ?_⟩
    · simpa [advance,hc] using (h z q hprev).1
    · simp [advance,hc,leaderNow]
  | some i =>
    have hkey : (leaderNow s).filter (TaggedFront.isLong s.config) = some z := by
      rw [← activeQueue_key]
      simpa [advance, hc, Option.map_map, Function.comp_def] using
        congrArg (Option.map Prod.fst) hq
    have data : leaderNow s = some z ∧ TaggedFront.isLong s.config z = true := by
      cases hlo : leaderNow s with
      | none => simp [hlo] at hkey
      | some j =>
        by_cases hl : TaggedFront.isLong s.config j = true
        · have hj : j = z := by simpa [hlo, Option.filter, hl] using hkey
          subst j
          exact ⟨rfl, hl⟩
        · simp [hlo, Option.filter, hl] at hkey
    refine ⟨?_, ?_⟩
    · simpa [advance,hc] using data.1
    · intro hnext
      rw [projection_step]
      refine isLong_step_of_surviving_leader hn s.config cov e z data.2 ?_
      have hlead := leaderNow_live hnext
      simpa only [projection_step] using hlead

private theorem episodeBoth_track {p c1 n : Nat} (hn : 4 ≤ n)
    (s : Obs p c1 n) (w : List (Fin n)) (h : EpisodeAccount s)
    (hm : EpisodeMemory s) (hc : MCOV s.config) :
    EpisodeAccount (track s w) ∧ EpisodeMemory (track s w) := by
  induction w generalizing s with
  | nil => exact ⟨h,hm⟩
  | cons e w ih =>
    exact ih _ (episodeAccount_step e h hm) (episodeMemory_step hn s hc e hm)
      (by rw [projection_step]; exact mcov_step hn s.config hc e)

/-- Literal trace: exact one-long-episode-per-tenure inequality after
the cover. This does not bound the number of tenures themselves. -/
theorem trace_episodes_le_tenures {p c1 n : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (i : Fin n) (w : List (Fin n)) (hc : MCOV x) :
    (track (init x i) w).episodes ≤ (track (init x i) w).tenureCount := by
  have h : EpisodeAccount (init x i) := by simp [EpisodeAccount,init]
  have hm : EpisodeMemory (init x i) := by simp [EpisodeMemory,init]
  have hacc := (episodeBoth_track hn (init x i) w h hm hc).1
  unfold EpisodeAccount at hacc
  omega

end L4.TaggedTrace
