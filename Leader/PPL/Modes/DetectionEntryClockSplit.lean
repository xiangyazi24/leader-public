import Leader.PPL.Modes.DetectionEntrySplit
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.TransitionFacts
import Lean


namespace PPL.Modes.Lemma6


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.Lemma9


/-!
The statement in Lemma6Split is true as written.


On a failing leaderless, signal-free word, the tracked agent's responder-side
incident edge is exactly H and its initiator-side incident edge is exactly T.
The stronger invariant below identifies the literal clock/hits state with the
lottery parser; the public clockSuffixTickLotteryBridge is only one-sided and
is therefore not sufficient by itself for this reverse failure implication.
-/


/-! ## Boolean fold facts -/


private theorem foldlOr_true
    (xs : List Bool) :
    xs.foldl (fun a b => a || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simpa [List.foldl_cons] using ih


private theorem foldlAnd_false
    (xs : List Bool) :
    xs.foldl (fun a b => a && b) false = false := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simpa [List.foldl_cons] using ih


private theorem foldlOrFalse_allFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a || b) false = false) :
    ∀ b, b ∈ xs → b = false := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u || v) false = false := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            rfl
          · exact ih ht b hb
      | true =>
          have ht : xs.foldl (fun u v => u || v) true = true :=
            foldlOr_true xs
          have hf : False := by
            rw [List.foldl_cons, ha] at h
            simp only [Bool.false_or, Bool.true_and] at h
            rw [ht] at h
            cases h
          exact hf.elim


private theorem foldlAndTrue_allTrue
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = true) :
    ∀ b, b ∈ xs → b = true := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht : xs.foldl (fun u v => u && v) false = false :=
            foldlAnd_false xs
          have hf : False := by
            rw [List.foldl_cons, ha] at h
            simp only [Bool.false_or, Bool.true_and] at h
            rw [ht] at h
            cases h
          exact hf.elim
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = true := by
            simpa [List.foldl_cons, ha] using h
          intro b hb
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            rfl
          · exact ih ht b hb


private theorem foldlAndTrue_of_allTrue
    (xs : List Bool) :
    (∀ b, b ∈ xs → b = true) →
      xs.foldl (fun a b => a && b) true = true := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons a xs ih =>
      intro h
      have ha : a = true := h a (by simp)
      have ht : ∀ b, b ∈ xs → b = true := by
        intro b hb
        exact h b (by simp [hb])
      simpa [List.foldl_cons, ha] using ih ht


private theorem foldlAndFalse_existsFalse
    (xs : List Bool)
    (h : xs.foldl (fun a b => a && b) true = false) :
    ∃ b, b ∈ xs ∧ b = false := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      cases ha : a with
      | false =>
          exact ⟨false, by simp, rfl⟩
      | true =>
          have ht :
              xs.foldl (fun u v => u && v) true = false := by
            simpa [List.foldl_cons, ha] using h
          obtain ⟨b, hb, hbf⟩ := ih ht
          exact ⟨b, by simp [hb], hbf⟩


private theorem leaderPresent_false_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : leaderPresent C = false)
    (i : Fin n) :
    (C i).leader = false := by
  unfold leaderPresent at h
  have hall :=
    foldlOrFalse_allFalse
      (List.ofFn (fun j : Fin n => (C j).leader)) h
  apply hall (C i).leader
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩


private theorem signalFree_true_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : signalFreeB C = true)
    (i : Fin n) :
    (C i).signalR.val = 0 := by
  unfold signalFreeB allAgentsB at h
  have hall :=
    foldlAndTrue_allTrue
      (List.ofFn
        (fun j : Fin n => decide ((C j).signalR.val = 0))) h
  have hm :
      decide ((C i).signalR.val = 0) ∈
        List.ofFn
          (fun j : Fin n => decide ((C j).signalR.val = 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  have hd := hall _ hm
  exact of_decide_eq_true hd


private theorem signalFree_true_of_at
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : ∀ i : Fin n, (C i).signalR.val = 0) :
    signalFreeB C = true := by
  unfold signalFreeB allAgentsB
  apply foldlAndTrue_of_allTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  simp [h i]


private theorem allDetect_false_exists_construct
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : allDetectB C = false) :
    ∃ x : Fin n, (C x).mode = false := by
  unfold allDetectB allAgentsB at h
  obtain ⟨b, hbmem, hbf⟩ :=
    foldlAndFalse_existsFalse
      (List.ofFn
        (fun i : Fin n => decide ((C i).mode = true))) h
  rw [List.mem_ofFn] at hbmem
  obtain ⟨x, hx⟩ := hbmem
  have hdec :
      decide ((C x).mode = true) = false :=
    hx.trans hbf
  cases hm : (C x).mode with
  | false =>
      exact ⟨x, hm⟩
  | true =>
      simp [hm] at hdec


private theorem goodFalse_leaderless
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h : lemma6GoodB C = false) :
    leaderPresent C = false := by
  unfold lemma6GoodB at h
  cases hl : leaderPresent C with
  | false =>
      rfl
  | true =>
      simp [hl] at h


private theorem goodFalse_allDetect_false
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (hgood : lemma6GoodB C = false)
    (hfree : signalFreeB C = true) :
    allDetectB C = false := by
  have hl := goodFalse_leaderless C hgood
  unfold lemma6GoodB at hgood
  simpa [hl, hfree] using hgood


private theorem reachesAux_false_current_good_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h : reachesAux ring C word = false) :
    lemma6GoodB C = false := by
  cases word with
  | nil =>
      simpa [reachesAux] using h
  | cons e rest =>
      cases hg : lemma6GoodB C with
      | false =>
          rfl
      | true =>
          simp [reachesAux, hg] at h


private theorem reachesAux_false_tail
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (rest : DetSchedule n)
    (h : reachesAux ring C (e :: rest) = false) :
    reachesAux ring (pplStep ring C e) rest = false := by
  have hg :=
    reachesAux_false_current_good_false ring C (e :: rest) h
  simpa [reachesAux, hg] using h


private theorem pplStep_eq_protocolStep
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    pplStep ring C e =
      (PPL.protocol psi kappa).step ring C e := by
  rfl


private theorem reachesAux_false_endpoint_good_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h : reachesAux ring C word = false) :
    lemma6GoodB (runPPL ring C word) = false := by
  induction word generalizing C with
  | nil =>
      simpa [reachesAux, runPPL, runPopulationSchedule] using h
  | cons e rest ih =>
      have ht := reachesAux_false_tail ring C e rest h
      simp only [runPPL, runPopulationSchedule]
      rw [← pplStep_eq_protocolStep ring C e]
      change
        lemma6GoodB (runPPL ring (pplStep ring C e) rest) = false
      exact ih (C := pplStep ring C e) ht


private theorem runPPL_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    runPPL ring C (u ++ v) =
      runPPL ring (runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, runPPL, runPopulationSchedule]
      exact ih (C := pplStep ring C e)


/-! ## Timer projection through the full literal pair transition -/


private structure TimerObs where
  clock : Nat
  hits : Nat
  mode : Bool
  signalR : Nat
  deriving DecidableEq


private def timerObs {psi kappa : Nat}
    (q : PPL.State psi kappa) : TimerObs where
  clock := q.clock.val
  hits := q.hits.val
  mode := q.mode
  signalR := q.signalR.val


private theorem timerObs_eq
    {a b : TimerObs}
    (hclock : a.clock = b.clock)
    (hhits : a.hits = b.hits)
    (hmode : a.mode = b.mode)
    (hsignalR : a.signalR = b.signalR) :
    a = b := by
  cases a with
  | mk ac ah am ar =>
      cases b with
      | mk bc bh bm br =>
          simp_all


private theorem moveToken_mode
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.mode = l.mode ∧ q.2.mode = r.mode := by
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields hpsi kind l r
  have him :=
    congrArg
      (fun z : PPL.State psi kappa => z.mode) hi
  have hleft : (PPL.moveToken hpsi kind l r).1.mode = l.mode := by
    cases kind <;>
      simpa [PPL.eraseKindToken] using him
  have hright : (PPL.moveToken hpsi kind l r).2.mode = r.mode := by
    rcases PPL.moveToken_responder_fields hpsi kind l r with hr | hr
    · have hm :=
        congrArg
          (fun z : PPL.State psi kappa => z.mode) hr
      cases kind <;>
        simpa [PPL.eraseKindTokenId, PPL.eraseKindToken] using hm
    · have hm :=
        congrArg
          (fun z : PPL.State psi kappa => z.mode) hr
      cases kind <;>
        simpa [PPL.eraseKindTokenId, PPL.eraseKindToken,
          PPL.birthFields] using hm
  exact ⟨hleft, hright⟩


private theorem moveToken_timer
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    timerObs q.1 = timerObs l ∧
      timerObs q.2 = timerObs r := by
  dsimp only
  have hc := PPL.moveToken_clock_hits hpsi kind l r
  have hs := PPL.moveToken_signal_hits hpsi kind l r
  have hm := moveToken_mode hpsi kind l r
  dsimp only at hc
  constructor
  · apply timerObs_eq
    · exact congrArg Fin.val hc.1
    · exact congrArg Fin.val hc.2.1
    · exact hm.1
    · exact congrArg Fin.val hs.1
  · apply timerObs_eq
    · exact congrArg Fin.val hc.2.2.1
    · exact congrArg Fin.val hc.2.2.2
    · exact hm.2
    · exact congrArg Fin.val hs.2.2.1


private def timerPreTokenPair
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)


private theorem timerLine6
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    timerObs s.left = timerObs d.1 ∧
      timerObs s.right = timerObs d.2 := by
  dsimp only [PPL.createLeaderThroughLine6]
  split
  · constructor
    · rfl
    · apply timerObs_eq <;> rfl
  · exact ⟨rfl, rfl⟩


private theorem timerPreTokenPair_fields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := timerPreTokenPair hpsi l r
    timerObs q.1 = timerObs d.1 ∧
      timerObs q.2 = timerObs d.2 := by
  let s := PPL.createLeaderThroughLine6 hpsi l r
  have hs := timerLine6 hpsi l r
  have hp :
      let q := timerPreTokenPair hpsi l r
      timerObs q.1 = timerObs s.left ∧
        timerObs q.2 = timerObs s.right := by
    dsimp only [timerPreTokenPair]
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals try (split <;> try dsimp only)
    all_goals exact ⟨rfl, rfl⟩
  dsimp only at hs hp ⊢
  exact ⟨hp.1.trans hs.1, hp.2.trans hs.2⟩


private theorem createLeader_timer
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    timerObs q.1 = timerObs d.1 ∧
      timerObs q.2 = timerObs d.2 := by
  let p := timerPreTokenPair hpsi l r
  let b := PPL.moveToken hpsi .black p.1 p.2
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hdef : PPL.createLeader hpsi l r = w := by
    rfl
  have hp := timerPreTokenPair_fields hpsi l r
  have hb := moveToken_timer hpsi .black p.1 p.2
  have hw := moveToken_timer hpsi .white b.1 b.2
  dsimp only at hp hb hw
  rw [hdef]
  exact
    ⟨hw.1.trans (hb.1.trans hp.1),
      hw.2.trans (hb.2.trans hp.2)⟩


private def timerOther {psi kappa : Nat}
    (z : PPL.Elim.OtherFields psi kappa) : TimerObs where
  clock := z.clock.val
  hits := z.hits.val
  mode := z.mode
  signalR := z.signalR.val


private theorem eliminateLeaders_timer
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    timerObs q.1 = timerObs l ∧
      timerObs q.2 = timerObs r := by
  dsimp only
  have hl := PPL.Elim.otherView_eliminateLeaders_left l r
  have hr := PPL.Elim.otherView_eliminateLeaders_right l r
  constructor
  · have h := congrArg timerOther hl
    simpa [timerOther, timerObs, PPL.Elim.otherView] using h
  · have h := congrArg timerOther hr
    simpa [timerOther, timerObs, PPL.Elim.otherView] using h


private theorem ppl_timer_projection
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let q := PPL.ppl hpsi l r
    timerObs q.1 = timerObs d.1 ∧
      timerObs q.2 = timerObs d.2 := by
  let c := PPL.createLeader hpsi l r
  let q := PPL.eliminateLeaders c.1 c.2
  have hc := createLeader_timer hpsi l r
  have he := eliminateLeaders_timer c.1 c.2
  have hdef : PPL.ppl hpsi l r = q := by
    rfl
  dsimp only at hc he
  dsimp only
  rw [hdef]
  exact
    ⟨he.1.trans hc.1, he.2.trans hc.2⟩


/-! ## Exact signal-free H/T timer -/


private def timerStep
    (psi kappa : Nat) (v : TimerObs) (head : Bool) :
    TimerObs :=
  if head then
    let bumped := Nat.min (v.hits + 1) psi
    if bumped = psi then
      let clk := Nat.min (v.clock + 1) kappa
      { clock := clk
        hits := 0
        mode := clk == kappa
        signalR := 0 }
    else
      { clock := v.clock
        hits := bumped
        mode := v.clock == kappa
        signalR := 0 }
  else
    { clock := v.clock
      hits := 0
      mode := v.clock == kappa
      signalR := 0 }


private theorem timerStep_signalR_zero
    (psi kappa : Nat)
    (v : TimerObs)
    (b : Bool) :
    (timerStep psi kappa v b).signalR = 0 := by
  cases b with
  | false =>
      rfl
  | true =>
      simp only [timerStep, if_true]
      split <;> rfl


private theorem determineMode_noSignal_timer
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlead : l.leader = false)
    (hlsig : l.signalR.val = 0)
    (hrsig : r.signalR.val = 0) :
    let d := PPL.determineMode l r
    timerObs d.1 = timerStep psi kappa (timerObs l) false ∧
      timerObs d.2 = timerStep psi kappa (timerObs r) true := by
  have hls0 : l.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hlsig
  have hrs0 : r.signalR = (0 : Fin (kappa + 1)) := by
    apply Fin.ext
    simpa using hrsig
  by_cases hhit : Nat.min (r.hits.val + 1) psi = psi
  · simp only [PPL.determineMode, hlead]
    unfoldFinishModes
    simp [hls0, hrs0, timerObs, timerStep, hhit] <;> omega
  · simp only [PPL.determineMode, hlead]
    unfoldFinishModes
    simp [hls0, hrs0, timerObs, timerStep, hhit] <;> omega


private theorem ppl_noSignal_timer
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hlead : l.leader = false)
    (hlsig : l.signalR.val = 0)
    (hrsig : r.signalR.val = 0) :
    let q := PPL.ppl hpsi l r
    timerObs q.1 = timerStep psi kappa (timerObs l) false ∧
      timerObs q.2 = timerStep psi kappa (timerObs r) true := by
  have hp := ppl_timer_projection hpsi l r
  have hd :=
    determineMode_noSignal_timer hpsi l r hlead hlsig hrsig
  dsimp only at hp hd ⊢
  exact ⟨hp.1.trans hd.1, hp.2.trans hd.2⟩


private theorem leftNeighbor_ne_self6
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (i : Fin n) :
    ring.leftNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + n - 1) % n = i.val at hv
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega


private theorem leftNeighbor_rightNeighbor6
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem rightNeighbor_leftNeighbor6
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    have hlt : i.val - 1 < n := by omega
    have hleft : (i.val + n - 1) % n = i.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]


private theorem pplStep_timer_at
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e x : Fin n)
    (hleader : ∀ i : Fin n, (C i).leader = false)
    (hsignal : ∀ i : Fin n, (C i).signalR.val = 0) :
    timerObs (pplStep ring C e x) =
      match incidentBit ring x e with
      | none => timerObs (C x)
      | some b => timerStep psi kappa (timerObs (C x)) b := by
  by_cases hl : e = ring.leftNeighbor x
  · subst e
    have hne : ring.leftNeighbor x ≠ x :=
      leftNeighbor_ne_self6 ring (by omega) x
    have hxne : x ≠ ring.leftNeighbor x := by
      intro h
      exact hne h.symm
    have hpair :=
      ppl_noSignal_timer hpsi
        (C (ring.leftNeighbor x)) (C x)
        (hleader (ring.leftNeighbor x))
        (hsignal (ring.leftNeighbor x))
        (hsignal x)
    have hj : ring.rightNeighbor (ring.leftNeighbor x) = x :=
      rightNeighbor_leftNeighbor6 ring x
    have hstep :
        timerObs
            (pplStep ring C (ring.leftNeighbor x) x) =
          timerObs
            (PPL.ppl hpsi
              (C (ring.leftNeighbor x)) (C x)).2 := by
      simp [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hne, hxne, hj]
    simpa [incidentBit] using hstep.trans hpair.2
  · by_cases hx : e = x
    · subst e
      have hxl : x ≠ ring.leftNeighbor x := by
        intro h
        exact (leftNeighbor_ne_self6 ring (by omega) x) h.symm
      have hpair :=
        ppl_noSignal_timer hpsi
          (C x) (C (ring.rightNeighbor x))
          (hleader x) (hsignal x)
          (hsignal (ring.rightNeighbor x))
      have hstep :
          timerObs (pplStep ring C x x) =
            timerObs
              (PPL.ppl hpsi
                (C x) (C (ring.rightNeighbor x))).1 := by
        simp [pplStep, PopulationProtocol.step,
          PPL.protocol, PPL.transition, hpsi]
      simpa [incidentBit, hxl] using hstep.trans hpair.1
    · have hxr : x ≠ ring.rightNeighbor e := by
        intro h
        have hh : ring.leftNeighbor x = e := by
          calc
            ring.leftNeighbor x =
                ring.leftNeighbor (ring.rightNeighbor e) := by rw [h]
            _ = e := leftNeighbor_rightNeighbor6 ring e
        exact hl hh.symm
      have hxe : x ≠ e := by
        intro h
        exact hx h.symm
      have hsame : pplStep ring C e x = C x := by
        simp [pplStep, PopulationProtocol.step,
          PPL.protocol, hxe, hxr]
      simpa [incidentBit, hl, hx, hsame]


private theorem pplStep_signal_zero
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hleader : ∀ i : Fin n, (C i).leader = false)
    (hsignal : ∀ i : Fin n, (C i).signalR.val = 0) :
    ∀ i : Fin n, (pplStep ring C e i).signalR.val = 0 := by
  intro i
  have ht :=
    congrArg TimerObs.signalR
      (pplStep_timer_at hn3 hpsi ring C e i hleader hsignal)
  cases hb : incidentBit ring i e with
  | none =>
      rw [hb] at ht
      change
        (pplStep ring C e i).signalR.val = (C i).signalR.val at ht
      exact ht.trans (hsignal i)
  | some b =>
      rw [hb] at ht
      change
        (pplStep ring C e i).signalR.val =
          (timerStep psi kappa (timerObs (C i)) b).signalR at ht
      exact ht.trans
        (timerStep_signalR_zero psi kappa (timerObs (C i)) b)


private theorem pplStep_signalFree
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hleader : leaderPresent C = false)
    (hfree : signalFreeB C = true) :
    signalFreeB (pplStep ring C e) = true := by
  apply signalFree_true_of_at
  apply pplStep_signal_zero hn3 hpsi ring C e
  · exact leaderPresent_false_at C hleader
  · exact signalFree_true_at C hfree


private theorem runPPL_signalFree_of_failure
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hfree : signalFreeB C = true)
    (hfail : reachesAux ring C word = false) :
    signalFreeB (runPPL ring C word) = true := by
  induction word generalizing C with
  | nil =>
      simpa [runPPL, runPopulationSchedule] using hfree
  | cons e rest ih =>
      have hgood :=
        reachesAux_false_current_good_false ring C (e :: rest) hfail
      have hleader := goodFalse_leaderless C hgood
      have hnextFree :=
        pplStep_signalFree hn3 hpsi ring C e hleader hfree
      have htail :=
        reachesAux_false_tail ring C e rest hfail
      simp only [runPPL, runPopulationSchedule]
      rw [← pplStep_eq_protocolStep ring C e]
      change
        signalFreeB (runPPL ring (pplStep ring C e) rest) = true
      exact ih (C := pplStep ring C e) hnextFree htail


/-! ## Stopped encounter record = raw fixed-agent H/T record on failure -/


private def rawEncounterBits {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n) : DetSchedule n → List Bool
  | [] => []
  | e :: rest =>
      match incidentBit ring x e with
      | none => rawEncounterBits ring x rest
      | some b => b :: rawEncounterBits ring x rest


private theorem incidentLetter_eq_incidentBit_isSome
    {n : Nat}
    (ring : DirectedRing n)
    (x e : Fin n) :
    incidentLetter ring x e =
      (incidentBit ring x e).isSome := by
  by_cases hl : e = ring.leftNeighbor x
  · simp [incidentLetter, incidentBit, twoEdgeLetter, hl]
  · by_cases hx : e = x
    · subst e
      simp [incidentLetter, incidentBit, twoEdgeLetter, hl]
    · simp [incidentLetter, incidentBit, twoEdgeLetter, hl, hx]


private theorem stoppedRecordAux_eq_raw_of_noStop
    {n : Nat}
    (ring : DirectedRing n)
    (x : Fin n)
    (stop : List (Fin n) → Bool) :
    ∀ (pre : List (Fin n)) (word : DetSchedule n),
      stopReachedAux stop pre word = false →
      stoppedEncounterBitsAux ring (fun _ => x) stop pre word =
          rawEncounterBits ring x word ∧
        stoppedPredictableHostHitsAux
            ring (fun _ => x) stop pre word =
          (rawEncounterBits ring x word).length := by
  intro pre word hstop
  induction word generalizing pre with
  | nil =>
      exact ⟨rfl, rfl⟩
  | cons e rest ih =>
      cases hs : stop pre with
      | true =>
          have hf : False := by
            simpa [stopReachedAux, hs] using hstop
          exact hf.elim
      | false =>
          have ht :
              stopReachedAux stop (pre ++ [e]) rest = false := by
            simpa [stopReachedAux, hs] using hstop
          have hih := ih (pre := pre ++ [e]) ht
          cases hb : incidentBit ring x e with
          | none =>
              have hil : incidentLetter ring x e = false := by
                rw [incidentLetter_eq_incidentBit_isSome]
                simp [hb]
              simpa [stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                rawEncounterBits, hs, hb, hil] using hih
          | some b =>
              have hil : incidentLetter ring x e = true := by
                rw [incidentLetter_eq_incidentBit_isSome]
                simp [hb]
              constructor
              · simp [stoppedEncounterBitsAux, rawEncounterBits,
                  hs, hb, hih.1]
              · simpa [stoppedPredictableHostHitsAux, rawEncounterBits,
                  hs, hil, hb, hih.2, Nat.add_comm]


private theorem reachesAux_false_stopReachedAux
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi kappa) :
    ∀ (pre : DetSchedule n) (word : DetSchedule n),
      reachesAux ring (runPPL ring C0 pre) word = false →
      stopReachedAux (firstLeaderStop ring C0) pre word = false := by
  intro pre word hfail
  induction word generalizing pre with
  | nil =>
      have hgood :
          lemma6GoodB (runPPL ring C0 pre) = false := by
        simpa [reachesAux] using hfail
      have hl :=
        goodFalse_leaderless (runPPL ring C0 pre) hgood
      simpa [stopReachedAux, firstLeaderStop] using hl
  | cons e rest ih =>
      let D := runPPL ring C0 pre
      have hgood :
          lemma6GoodB D = false :=
        reachesAux_false_current_good_false
          ring D (e :: rest) hfail
      have hl : leaderPresent D = false :=
        goodFalse_leaderless D hgood
      have htail :
          reachesAux ring (pplStep ring D e) rest = false :=
        reachesAux_false_tail ring D e rest hfail
      have hcfg :
          runPPL ring C0 (pre ++ [e]) =
            pplStep ring D e := by
        dsimp [D]
        rw [runPPL_append]
        rfl
      have hih :
          stopReachedAux
              (firstLeaderStop ring C0)
              (pre ++ [e]) rest = false := by
        apply ih (pre := pre ++ [e])
        simpa [hcfg] using htail
      simpa [stopReachedAux, firstLeaderStop, D, hl] using hih


private theorem reachesAux_false_stopReached
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hfail : reachesAux ring C word = false) :
    stopReached (firstLeaderStop ring C) word = false := by
  have h :=
    reachesAux_false_stopReachedAux
      ring C [] word
      (by
        simpa [runPPL, runPopulationSchedule] using hfail)
  simpa [stopReached] using h


private theorem stoppedRecord_eq_raw_of_failure
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x : Fin n)
    (word : DetSchedule n)
    (hfail : reachesAux ring C word = false) :
    let host : List (Fin n) → Fin n := fun _ => x
    let stop := firstLeaderStop ring C
    stoppedEncounterBits ring host stop word =
        rawEncounterBits ring x word ∧
      stoppedPredictableHostHits ring host stop word =
        (rawEncounterBits ring x word).length := by
  dsimp only
  have hstop :=
    reachesAux_false_stopReached ring C word hfail
  have h :=
    stoppedRecordAux_eq_raw_of_noStop
      ring x (firstLeaderStop ring C) [] word
      (by simpa [stopReached] using hstop)
  exact h


/-! ## Full physical run = timerRun on raw H/T marks -/


private def timerRun (psi kappa : Nat) :
    TimerObs → List Bool → TimerObs
  | v, [] => v
  | v, b :: rest =>
      timerRun psi kappa (timerStep psi kappa v b) rest


private theorem runPPL_timer_eq_timerRun
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (x : Fin n)
    (word : DetSchedule n)
    (hfree : signalFreeB C = true)
    (hfail : reachesAux ring C word = false) :
    timerObs (runPPL ring C word x) =
      timerRun psi kappa (timerObs (C x))
        (rawEncounterBits ring x word) := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      have hgood :=
        reachesAux_false_current_good_false
          ring C (e :: rest) hfail
      have hleader := goodFalse_leaderless C hgood
      have hleaders := leaderPresent_false_at C hleader
      have hsignals := signalFree_true_at C hfree
      have hlocal :=
        pplStep_timer_at hn3 hpsi ring C e x hleaders hsignals
      have hnextFree :=
        pplStep_signalFree hn3 hpsi ring C e hleader hfree
      have htail :=
        reachesAux_false_tail ring C e rest hfail
      have hih :=
        ih (C := pplStep ring C e) hnextFree htail
      simp only [runPPL, runPopulationSchedule]
      rw [← pplStep_eq_protocolStep ring C e]
      change
        timerObs (runPPL ring (pplStep ring C e) rest x) =
          timerRun psi kappa (timerObs (C x))
            (rawEncounterBits ring x (e :: rest))
      rw [hih]
      cases hb : incidentBit ring x e with
      | none =>
          rw [hb] at hlocal
          simpa [rawEncounterBits, hb, timerRun, hlocal]
      | some b =>
          rw [hb] at hlocal
          simpa [rawEncounterBits, hb, timerRun, hlocal]


/-! ## Pure timer/lottery arithmetic -/


private def TimerLotteryInvariant
    (base kappa : Nat) (v : TimerObs)
    (s : LotteryState) : Prop :=
  s.headRun = v.hits ∧
    v.clock = Nat.min (base + s.wins) kappa


private theorem timerStep_bounds
    (psi kappa : Nat)
    (v : TimerObs)
    (b : Bool)
    (hc : v.clock ≤ kappa)
    (_hh : v.hits ≤ psi) :
    (timerStep psi kappa v b).clock ≤ kappa ∧
      (timerStep psi kappa v b).hits ≤ psi := by
  cases b with
  | false =>
      exact ⟨hc, Nat.zero_le _⟩
  | true =>
      simp only [timerStep, if_true]
      split
      · exact ⟨Nat.min_le_right _ _, Nat.zero_le _⟩
      · exact ⟨hc, Nat.min_le_right _ _⟩


private theorem timerLotteryInvariant_step
    (psi kappa base : Nat)
    (v : TimerObs)
    (s : LotteryState)
    (b : Bool)
    (hc : v.clock ≤ kappa)
    (hh : v.hits ≤ psi)
    (hinv : TimerLotteryInvariant base kappa v s) :
    TimerLotteryInvariant base kappa
      (timerStep psi kappa v b)
      (lotteryStep psi s b) := by
  rcases hinv with ⟨hhead, hclock⟩
  cases b with
  | false =>
      simp [TimerLotteryInvariant, timerStep, lotteryStep, hclock]
  | true =>
      by_cases hwin : psi ≤ s.headRun + 1
      · have hwin' : psi ≤ v.hits + 1 := by
          simpa [hhead] using hwin
        have hbump :
            Nat.min (v.hits + 1) psi = psi :=
          Nat.min_eq_right hwin'
        have hclockStep :
            Nat.min (v.clock + 1) kappa =
              Nat.min (base + (s.wins + 1)) kappa := by
          by_cases hcap : kappa ≤ base + s.wins
          · have hmin :
                Nat.min (base + s.wins) kappa = kappa :=
              Nat.min_eq_right hcap
            calc
              Nat.min (v.clock + 1) kappa
                  = kappa := by
                    rw [hclock, hmin]
                    exact Nat.min_eq_right (by omega)
              _ = Nat.min (base + (s.wins + 1)) kappa :=
                    (Nat.min_eq_right (by omega)).symm
          · have hle : base + s.wins ≤ kappa := by omega
            have hvclock : v.clock = base + s.wins := by
              exact hclock.trans (Nat.min_eq_left hle)
            simpa [hvclock, Nat.add_assoc]
        simp [TimerLotteryInvariant, timerStep, lotteryStep,
          hwin, hbump, hclockStep]
      · have hwin' : ¬ psi ≤ v.hits + 1 := by
          simpa [hhead] using hwin
        have hlt : v.hits + 1 < psi := by omega
        have hneq : v.hits + 1 ≠ psi := by omega
        have hbump :
            Nat.min (v.hits + 1) psi = v.hits + 1 :=
          Nat.min_eq_left (by omega)
        simp [TimerLotteryInvariant, timerStep, lotteryStep,
          hwin, hwin', hneq, hbump, hhead, hclock]


private theorem timerRun_lotteryInvariant
    (psi kappa base : Nat)
    (v : TimerObs)
    (s : LotteryState)
    (bits : List Bool)
    (hc : v.clock ≤ kappa)
    (hh : v.hits ≤ psi)
    (hinv : TimerLotteryInvariant base kappa v s) :
    TimerLotteryInvariant base kappa
      (timerRun psi kappa v bits)
      (lotteryRun psi s bits) := by
  induction bits generalizing v s with
  | nil =>
      simpa [timerRun, lotteryRun] using hinv
  | cons b rest ih =>
      have hstep :=
        timerLotteryInvariant_step
          psi kappa base v s b hc hh hinv
      have hbounds :=
        timerStep_bounds psi kappa v b hc hh
      simpa [timerRun, lotteryRun] using
        ih
          (v := timerStep psi kappa v b)
          (s := lotteryStep psi s b)
          hbounds.1 hbounds.2 hstep


private theorem timerRun_mode_normalized
    (psi kappa : Nat)
    (v : TimerObs)
    (bits : List Bool)
    (hne : bits ≠ []) :
    (timerRun psi kappa v bits).mode =
      ((timerRun psi kappa v bits).clock == kappa) := by
  induction bits generalizing v with
  | nil =>
      exact False.elim (hne rfl)
  | cons b rest ih =>
      cases rest with
      | nil =>
          cases b <;>
            simp [timerRun, timerStep] <;>
            split <;> rfl
      | cons c cs =>
          simpa [timerRun] using
            ih
              (v := timerStep psi kappa v b)
              (by simp)


private theorem lotteryRun_append
    (k : Nat)
    (s : LotteryState)
    (u v : List Bool) :
    lotteryRun k s (u ++ v) =
      lotteryRun k (lotteryRun k s u) v := by
  induction u generalizing s with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [lotteryRun, ih]


private theorem lotteryStep_wins_mono
    (k : Nat)
    (s : LotteryState)
    (b : Bool) :
    s.wins ≤ (lotteryStep k s b).wins := by
  cases b with
  | false =>
      simpa [lotteryStep] using (Nat.le_refl s.wins)
  | true =>
      by_cases hwin : k ≤ s.headRun + 1
      · simpa [lotteryStep, hwin] using (Nat.le_succ s.wins)
      · simpa [lotteryStep, hwin] using (Nat.le_refl s.wins)


private theorem lotteryRun_wins_mono
    (k : Nat)
    (s : LotteryState)
    (bits : List Bool) :
    s.wins ≤ (lotteryRun k s bits).wins := by
  induction bits generalizing s with
  | nil =>
      exact Nat.le_refl _
  | cons b rest ih =>
      exact Nat.le_trans
        (lotteryStep_wins_mono k s b)
        (by
          simpa [lotteryRun] using
            ih (s := lotteryStep k s b))


private theorem lotteryRun_take_wins_le
    (k : Nat)
    (s : LotteryState)
    (bits : List Bool)
    (E : Nat) :
    (lotteryRun k s (bits.take E)).wins ≤
      (lotteryRun k s bits).wins := by
  have hm :=
    lotteryRun_wins_mono
      k (lotteryRun k s (bits.take E))
      (bits.drop E)
  have happ :=
    lotteryRun_append k s (bits.take E) (bits.drop E)
  have hdecomp :
      bits.take E ++ bits.drop E = bits :=
    List.take_append_drop E bits
  rw [hdecomp] at happ
  rw [← happ] at hm
  exact hm


private theorem lotteryWins_le_kappa_of_finalConstruct
    {psi kappa : Nat}
    (v : TimerObs)
    (bits : List Bool)
    (hc : v.clock ≤ kappa)
    (hh : v.hits ≤ psi)
    (hne : bits ≠ [])
    (hmode :
      (timerRun psi kappa v bits).mode = false) :
    (lotteryRun psi (lotteryOffset v.hits) bits).wins ≤ kappa := by
  let s0 := lotteryOffset v.hits
  have hinv0 :
      TimerLotteryInvariant v.clock kappa v s0 := by
    constructor
    · rfl
    · simp [s0, lotteryOffset, TimerLotteryInvariant,
        Nat.min_eq_left hc]
  have hinv :=
    timerRun_lotteryInvariant
      psi kappa v.clock v s0 bits hc hh hinv0
  have hnorm :=
    timerRun_mode_normalized psi kappa v bits hne
  by_cases hw :
      (lotteryRun psi s0 bits).wins ≤ kappa
  · simpa [s0] using hw
  · have harg :
        kappa ≤
          v.clock + (lotteryRun psi s0 bits).wins := by
      omega
    have hcap :
        (timerRun psi kappa v bits).clock = kappa := by
      calc
        (timerRun psi kappa v bits).clock =
            Nat.min
              (v.clock + (lotteryRun psi s0 bits).wins)
              kappa := hinv.2
        _ = kappa := Nat.min_eq_right harg
    have htrue :
        (timerRun psi kappa v bits).mode = true := by
      rw [hnorm, hcap]
      simp
    rw [hmode] at htrue
    cases htrue


/-! ## Headline -/


theorem lemma6ClockFailureSplit :
    Lemma6ClockFailureSplit := by
  intro n psi kappa c
  intro hn3 hpsi hkappa
  intro ring C word
  intro _hleader hfree hfail


  let D := runPPL ring C word


  have hDfree :
      signalFreeB D = true := by
    dsimp [D]
    exact
      runPPL_signalFree_of_failure
        hn3 hpsi ring C word hfree hfail


  have hDgood :
      lemma6GoodB D = false := by
    dsimp [D]
    exact
      reachesAux_false_endpoint_good_false
        ring C word hfail


  have hDetectFalse :
      allDetectB D = false :=
    goodFalse_allDetect_false D hDgood hDfree


  obtain ⟨x, hxmode⟩ :=
    allDetect_false_exists_construct D hDetectFalse


  refine ⟨x, hxmode, ?_⟩
  dsimp only


  have hrecord :=
    stoppedRecord_eq_raw_of_failure
      ring C x word hfail
  have hbits :
      stoppedEncounterBits
          ring (fun _ => x) (firstLeaderStop ring C) word =
        rawEncounterBits ring x word :=
    hrecord.1
  have hhits :
      stoppedPredictableHostHits
          ring (fun _ => x) (firstLeaderStop ring C) word =
        (rawEncounterBits ring x word).length :=
    hrecord.2


  by_cases hfew :
      stoppedPredictableHostHits
          ring (fun _ => x) (firstLeaderStop ring C) word <
        lemma9E psi c
  · exact Or.inl hfew
  · right
    have hEraw :
        lemma9E psi c ≤
          (rawEncounterBits ring x word).length := by
      rw [← hhits]
      omega
    constructor
    · rw [hbits]
      exact hEraw
    · by_cases hEzero : lemma9E psi c = 0
      · simp [hEzero, lotteryOffset, lotteryRun]
      · have hrawPos :
            0 < (rawEncounterBits ring x word).length := by
          omega
        have hrawNonempty :
            rawEncounterBits ring x word ≠ [] := by
          intro hz
          rw [hz] at hrawPos
          simp at hrawPos


        have hphysical :=
          runPPL_timer_eq_timerRun
            hn3 hpsi ring C x word hfree hfail


        let v := timerObs (C x)
        let raw := rawEncounterBits ring x word


        have hmachineMode :
            (timerRun psi kappa v raw).mode = false := by
          have hm := congrArg TimerObs.mode hphysical
          have hm' :
              false = (timerRun psi kappa v raw).mode := by
            simpa [D, v, raw, timerObs, hxmode] using hm
          exact hm'.symm


        have hvclock : v.clock ≤ kappa := by
          dsimp [v, timerObs]
          exact Nat.le_of_lt_succ (C x).clock.isLt
        have hvhits : v.hits ≤ psi := by
          dsimp [v, timerObs]
          exact Nat.le_of_lt_succ (C x).hits.isLt


        have hfullWins :
            (lotteryRun psi
              (lotteryOffset (C x).hits.val) raw).wins ≤ kappa := by
          have h :=
            lotteryWins_le_kappa_of_finalConstruct
              v raw hvclock hvhits
              (by simpa [raw] using hrawNonempty)
              hmachineMode
          simpa [v, timerObs] using h


        have hpref :
            (lotteryRun psi
              (lotteryOffset (C x).hits.val)
              (raw.take (lemma9E psi c))).wins ≤
              (lotteryRun psi
                (lotteryOffset (C x).hits.val) raw).wins :=
          lotteryRun_take_wins_le
            psi (lotteryOffset (C x).hits.val)
            raw (lemma9E psi c)


        calc
          (lotteryRun psi
              (lotteryOffset (C x).hits.val)
              ((stoppedEncounterBits
                ring (fun _ => x)
                (firstLeaderStop ring C) word).take
                  (lemma9E psi c))).wins
              =
            (lotteryRun psi
              (lotteryOffset (C x).hits.val)
              (raw.take (lemma9E psi c))).wins := by
                rw [hbits]
          _ ≤
            (lotteryRun psi
              (lotteryOffset (C x).hits.val) raw).wins := hpref
          _ ≤ kappa := hfullWins
          _ = lotteryTarget psi c := by
            simpa [lotteryTarget] using hkappa


#print axioms PPL.Modes.Lemma6.lemma6ClockFailureSplit


end PPL.Modes.Lemma6



