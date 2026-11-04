import Leader.PPL.Modes.SignalAbsorptionSplit
import Leader.PPL.Modes.SignalLineageLocal

namespace PPL.Modes.Lemma9

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage

private theorem rightNeighbor_ne_self_lineage
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (x : Fin n) :
    ring.rightNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : x.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : x.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem leftNeighbor_rightNeighbor_lineage
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor x) = x := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hx : x.val + 1 < n
  · rw [Nat.mod_eq_of_lt hx]
    have heq : x.val + 1 + n - 1 = n + x.val := by
      omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt x.isLt]
  · have hx' : x.val + 1 = n := by
      omega
    rw [hx', Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem rightNeighbor_leftNeighbor_lineage
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor x) = x := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hx : x.val = 0
  · rw [hx]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by
      omega
    rw [hs, Nat.mod_self]
  · have heq : x.val + n - 1 = n + (x.val - 1) := by
      omega
    have hlt : x.val - 1 < n := by
      omega
    have hleft :
        (x.val + n - 1) % n = x.val - 1 := by
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    rw [hleft]
    have hs : x.val - 1 + 1 = x.val := by
      omega
    rw [hs, Nat.mod_eq_of_lt x.isLt]

private theorem leftNeighbor_ne_self_lineage
    {n : Nat} (hn3 : 3 ≤ n)
    (ring : DirectedRing n) (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hr := congrArg (fun y => ring.rightNeighbor y) h
  rw [rightNeighbor_leftNeighbor_lineage ring x] at hr
  exact
    (rightNeighbor_ne_self_lineage hn3 ring x)
      hr.symm

private theorem ghostStep_wellFormed_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hwf : LineageWellFormed g) :
    LineageWellFormed (ghostStep ring g e) := by
  have hself :=
    rightNeighbor_ne_self_lineage hn3 ring e
  exact
    ⟨ownerMatchesPreserved ring g e hpsi hself hwf,
      noCloningPreserved ring g e hpsi hself hwf,
      issuedPreserved ring g e hpsi hself hwf⟩

private theorem ghostRun_invariants_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (word : DetSchedule n)
    (hwf : LineageWellFormed g)
    (hnext : ∀ x : Fin n, 0 < g.nextArm x) :
    LineageWellFormed (ghostRun ring g word) ∧
      (∀ x : Fin n,
        0 < (ghostRun ring g word).nextArm x) := by
  induction word generalizing g with
  | nil =>
      exact ⟨hwf, hnext⟩
  | cons e rest ih =>
      have hwf' :=
        ghostStep_wellFormed_lineage
          hn3 hpsi ring g e hwf
      have hnext' :
          ∀ x : Fin n,
            0 < (ghostStep ring g e).nextArm x := by
        intro x
        exact
          Nat.lt_of_lt_of_le
            (hnext x)
            (ghostStep_nextArm_mono ring g e x)
      exact
        ih (g := ghostStep ring g e)
          hwf' hnext'

private theorem ghostRun_append_lineage
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (u v : DetSchedule n) :
    ghostRun ring g (u ++ v) =
      ghostRun ring (ghostRun ring g u) v := by
  induction u generalizing g with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, ghostRun]
      exact
        ih (g := ghostStep ring g e)

private theorem foldl_or_true_lineage
    (xs : List Bool) :
    xs.foldl (fun acc b => acc || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, Bool.true_or]
      exact ih

private theorem foldl_or_true_of_mem_lineage
    (xs : List Bool)
    (hmem : true ∈ xs) :
    xs.foldl (fun acc b => acc || b) false = true := by
  induction xs with
  | nil =>
      simp at hmem
  | cons b xs ih =>
      rcases List.mem_cons.mp hmem with hb | ht
      · subst b
        simp only [List.foldl_cons, Bool.false_or]
        exact foldl_or_true_lineage xs
      · cases b
        · simp only [List.foldl_cons, Bool.false_or]
          exact ih ht
        · simp only [List.foldl_cons, Bool.false_or]
          exact foldl_or_true_lineage xs

private theorem foldl_or_false_of_all_false_lineage
    (xs : List Bool)
    (hall : ∀ b, b ∈ xs → b = false) :
    xs.foldl (fun acc b => acc || b) false = false := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      have hb := hall b (by simp)
      rw [List.foldl_cons, hb, Bool.false_or]
      exact
        ih
          (fun y hy =>
            hall y (by simp [hy]))

private theorem tagAliveB_true_of_owner_lineage
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (tag : SignalTag n)
    (x : Fin n)
    (hx : g.owner x = some tag) :
    tagAliveB g tag = true := by
  unfold tagAliveB
  apply foldl_or_true_of_mem_lineage
  rw [List.mem_ofFn]
  refine ⟨x, ?_⟩
  simp [hx]

private theorem tagAliveB_false_of_no_owner_lineage
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (tag : SignalTag n)
    (hdead : ∀ x : Fin n, g.owner x ≠ some tag) :
    tagAliveB g tag = false := by
  unfold tagAliveB
  apply foldl_or_false_of_all_false_lineage
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨x, rfl⟩ := hb
  simp [hdead x]

private theorem owner_exists_of_tagAliveB_true_lineage
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (tag : SignalTag n)
    (halive : tagAliveB g tag = true) :
    ∃ x : Fin n, g.owner x = some tag := by
  apply Classical.byContradiction
  intro hnone
  have hdead :
      ∀ x : Fin n, g.owner x ≠ some tag := by
    intro x hx
    apply hnone
    exact ⟨x, hx⟩
  have hz :=
    tagAliveB_false_of_no_owner_lineage
      g tag hdead
  rw [hz] at halive
  contradiction

private noncomputable def lineageHost
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre : List (Fin n)) : Fin n := by
  classical
  let g := ghostRun ring (initialGhost C) pre
  exact
    if h :
        ∃ x : Fin n,
          g.owner x = some (lemma9Tag i) then
      Classical.choose h
    else
      i

private theorem tagAlive_of_stop_false_lineage
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre : List (Fin n))
    (hstop : lemma9Stop ring C i pre = false) :
    tagAliveB
        (ghostRun ring (initialGhost C) pre)
        (lemma9Tag i) = true := by
  unfold lemma9Stop at hstop
  cases h :
      tagAliveB
        (ghostRun ring (initialGhost C) pre)
        (lemma9Tag i) with
  | false =>
      simp [h] at hstop
  | true =>
      rfl

private theorem lineageHost_owner
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre : List (Fin n))
    (hstop : lemma9Stop ring C i pre = false) :
    (ghostRun ring (initialGhost C) pre).owner
        (lineageHost ring C i pre) =
      some (lemma9Tag i) := by
  classical
  have halive :=
    tagAlive_of_stop_false_lineage
      ring C i pre hstop
  have hex :=
    owner_exists_of_tagAliveB_true_lineage
      (ghostRun ring (initialGhost C) pre)
      (lemma9Tag i) halive
  unfold lineageHost
  dsimp only
  rw [dif_pos hex]
  exact Classical.choose_spec hex

private theorem lineageHost_nil_eq_origin
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hsignal : 0 < (C i).signalR.val) :
    lineageHost ring C i [] = i := by
  have hi :
      (initialGhost C).owner i =
        some (lemma9Tag i) := by
    simp [initialGhost, lemma9Tag, hsignal]
  have halive :=
    tagAliveB_true_of_owner_lineage
      (initialGhost C) (lemma9Tag i) i hi
  have hstop :
      lemma9Stop ring C i [] = false := by
    unfold lemma9Stop
    change
      (!tagAliveB (initialGhost C) (lemma9Tag i)) = false
    rw [halive]
    rfl
  have hh :=
    lineageHost_owner ring C i [] hstop
  change
    (initialGhost C).owner
        (lineageHost ring C i []) =
      some (lemma9Tag i) at hh
  have hnc :=
    initialGhost_noCloning C
      i (lineageHost ring C i [])
      (lemma9Tag i) hi hh
  exact hnc.symm

private theorem arm0_ne_fresh_lineage
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (i e : Fin n)
    (hnext : ∀ x : Fin n, 0 < g.nextArm x) :
    lemma9Tag i ≠ freshTag g e := by
  intro h
  have ha := congrArg SignalTag.arm h
  change 0 = g.nextArm e at ha
  have hp := hnext e
  omega

private theorem ghostStep_dead_preserved_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e i : Fin n)
    (hnext : ∀ x : Fin n, 0 < g.nextArm x)
    (hdead :
      ∀ x : Fin n,
        g.owner x ≠ some (lemma9Tag i)) :
    ∀ x : Fin n,
      (ghostStep ring g e).owner x ≠
        some (lemma9Tag i) := by
  intro x hx
  have hself :=
    rightNeighbor_ne_self_lineage hn3 ring e
  by_cases hxe : x = e
  · subst x
    rw [ghostStep_initiator_owner_none] at hx
    contradiction
  by_cases hxr : x = ring.rightNeighbor e
  · subst x
    have hwin :=
      responder_winner_of_some
        ring g e hself (lemma9Tag i) hx
    rcases
        winnerOwner_some_cases
          g e (ring.rightNeighbor e)
          (lemma9Tag i) hwin with
      hnew | hold
    · exact
        (arm0_ne_fresh_lineage
          g i e hnext)
          hnew.2
    · rcases hold with he | hr
      · exact (hdead e) he
      · exact (hdead (ring.rightNeighbor e)) hr
  · have hold :
        g.owner x = some (lemma9Tag i) := by
      rw [← ghostStep_owner_other ring g e x hxe hxr]
      exact hx
    exact (hdead x) hold

private theorem ghostRun_dead_preserved_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (word : DetSchedule n)
    (i : Fin n)
    (hnext : ∀ x : Fin n, 0 < g.nextArm x)
    (hdead :
      ∀ x : Fin n,
        g.owner x ≠ some (lemma9Tag i)) :
    ∀ x : Fin n,
      (ghostRun ring g word).owner x ≠
        some (lemma9Tag i) := by
  induction word generalizing g with
  | nil =>
      exact hdead
  | cons e rest ih =>
      have hdead' :=
        ghostStep_dead_preserved_lineage
          hn3 ring g e i hnext hdead
      have hnext' :
          ∀ x : Fin n,
            0 < (ghostStep ring g e).nextArm x := by
        intro x
        exact
          Nat.lt_of_lt_of_le
            (hnext x)
            (ghostStep_nextArm_mono ring g e x)
      exact
        ih
          (g := ghostStep ring g e)
          hnext' hdead'

private theorem prefix_alive_of_final_alive_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre word : DetSchedule n)
    (hfinal :
      tagAliveB
        (ghostRun ring (initialGhost C)
          (pre ++ word))
        (lemma9Tag i) = true) :
    tagAliveB
        (ghostRun ring (initialGhost C) pre)
        (lemma9Tag i) = true := by
  let g :=
    ghostRun ring (initialGhost C) pre
  cases hpre :
      tagAliveB g (lemma9Tag i) with
  | true =>
      rfl
  | false =>
      have hdead :
          ∀ x : Fin n,
            g.owner x ≠ some (lemma9Tag i) := by
        intro x hx
        have ht :=
          tagAliveB_true_of_owner_lineage
            g (lemma9Tag i) x hx
        rw [hpre] at ht
        contradiction
      have hinv :=
        ghostRun_invariants_lineage
          hn3 hpsi ring
          (initialGhost C) pre
          (initialGhost_wellFormed C)
          (by
            intro x
            simp [initialGhost])
      have hdeadFinal :=
        ghostRun_dead_preserved_lineage
          hn3 ring g word i
          (by
            simpa [g] using hinv.2)
          hdead
      have hz :=
        tagAliveB_false_of_no_owner_lineage
          (ghostRun ring g word)
          (lemma9Tag i)
          hdeadFinal
      have happ :=
        ghostRun_append_lineage
          ring (initialGhost C) pre word
      rw [happ] at hfinal
      dsimp [g] at hz
      rw [hz] at hfinal
      contradiction

private theorem stopReachedAux_false_of_final_alive_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (pre word : DetSchedule n)
    (hfinal :
      tagAliveB
        (ghostRun ring (initialGhost C)
          (pre ++ word))
        (lemma9Tag i) = true) :
    stopReachedAux
      (lemma9Stop ring C i) pre word = false := by
  induction word generalizing pre with
  | nil =>
      have halive :=
        prefix_alive_of_final_alive_lineage
          hn3 hpsi ring C i pre [] hfinal
      have hs :
          lemma9Stop ring C i pre = false := by
        simp [lemma9Stop, halive]
      simpa [stopReachedAux, hs]
  | cons e rest ih =>
      have halive :=
        prefix_alive_of_final_alive_lineage
          hn3 hpsi ring C i pre
          (e :: rest) hfinal
      have hs :
          lemma9Stop ring C i pre = false := by
        simp [lemma9Stop, halive]
      have hfinal' :
          tagAliveB
            (ghostRun ring (initialGhost C)
              ((pre ++ [e]) ++ rest))
            (lemma9Tag i) = true := by
        simpa [List.append_assoc] using hfinal
      have htail :=
        ih (pre := pre ++ [e]) hfinal'
      simp [stopReachedAux, hs, htail]

private theorem stopReached_false_of_final_alive_lineage
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (word : DetSchedule n)
    (hfinal :
      tagAliveB
        (ghostRun ring (initialGhost C) word)
        (lemma9Tag i) = true) :
    stopReached
      (lemma9Stop ring C i) word = false := by
  simpa [stopReached] using
    (stopReachedAux_false_of_final_alive_lineage
      hn3 hpsi ring C i [] word
      (by simpa using hfinal))

private theorem stop_false_of_stopReachedAux_false_lineage
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (pre word : DetSchedule n)
    (h :
      stopReachedAux stop pre word = false) :
    stop pre = false := by
  cases word with
  | nil =>
      simpa [stopReachedAux] using h
  | cons e rest =>
      cases hs : stop pre with
      | false =>
          rfl
      | true =>
          simp [stopReachedAux, hs] at h

private theorem stopReachedAux_tail_false_lineage
    {n : Nat}
    (stop : List (Fin n) → Bool)
    (pre : DetSchedule n)
    (e : Fin n)
    (rest : DetSchedule n)
    (h :
      stopReachedAux stop pre (e :: rest) = false) :
    stopReachedAux stop (pre ++ [e]) rest = false := by
  have hs :=
    stop_false_of_stopReachedAux_false_lineage
      stop pre (e :: rest) h
  simpa [stopReachedAux, hs] using h

private theorem signal_pos_of_owner_lineage
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (x : Fin n)
    (tag : SignalTag n)
    (hwf : LineageWellFormed g)
    (hx : g.owner x = some tag) :
    0 < (g.physical x).signalR.val := by
  have hne :
      (g.physical x).signalR.val ≠ 0 := by
    intro hz
    have hn := (hwf.1 x).2 hz
    rw [hx] at hn
    contradiction
  omega

private theorem ghostStep_responder_projection_lineage
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    let j := ring.rightNeighbor e
    let d :=
      PPL.determineMode
        (g.physical e) (g.physical j)
    ((ghostStep ring g e).physical j).signalR =
        d.2.signalR ∧
      ((ghostStep ring g e).physical j).hits =
        d.2.hits := by
  dsimp only
  have hs :=
    step_signal_projection_of_stable
      postDetermineModeSignalStable
      hpsi ring g.physical e hself
  dsimp only at hs
  change
    (step ring g.physical e
        (ring.rightNeighbor e)).signalR =
          (PPL.determineMode
            (g.physical e)
            (g.physical
              (ring.rightNeighbor e))).2.signalR ∧
      (step ring g.physical e
        (ring.rightNeighbor e)).hits =
          (PPL.determineMode
            (g.physical e)
            (g.physical
              (ring.rightNeighbor e))).2.hits
  exact hs.2.2

private theorem bumpedHits_eq_psi_iff_lineage
    {psi kappa : Nat}
    (q : PPL.State psi kappa) :
    bumpedHitsVal q = psi ↔
      psi ≤ q.hits.val + 1 := by
  unfold bumpedHitsVal
  constructor
  · intro h
    calc
      psi = Nat.min (q.hits.val + 1) psi :=
        h.symm
      _ ≤ q.hits.val + 1 :=
        Nat.min_le_left _ _
  · intro h
    exact Nat.min_eq_right h

private def lineageLotteryAdvance
    (psi : Nat) (s : LotteryState)
    (b : Option Bool) : LotteryState :=
  match b with
  | none => s
  | some bit => lotteryStep psi s bit

private theorem lineage_T_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (g : GhostConfig n psi kappa)
    (x y i : Fin n)
    (hwf : LineageWellFormed g)
    (hx : g.owner x = some (lemma9Tag i))
    (hy :
      (ghostStep ring g x).owner y =
        some (lemma9Tag i))
    (s : LotteryState)
    (hsync : s.headRun = (g.physical x).hits.val) :
    let s' := lotteryStep psi s false
    s'.headRun =
        ((ghostStep ring g x).physical y).hits.val ∧
      s'.wins +
          ((ghostStep ring g x).physical y).signalR.val ≤
        s.wins + (g.physical x).signalR.val := by
  have hself :=
    rightNeighbor_ne_self_lineage hn3 ring x
  have hyresp :
      y = ring.rightNeighbor x := by
    by_cases hyx : y = x
    · subst y
      rw [ghostStep_initiator_owner_none] at hy
      contradiction
    by_cases hyr : y = ring.rightNeighbor x
    · exact hyr
    · have hold :
          g.owner y = some (lemma9Tag i) := by
        rw [← ghostStep_owner_other
          ring g x y hyx hyr]
        exact hy
      have hxy :=
        hwf.2.1 x y (lemma9Tag i)
          hx hold
      exact False.elim (hyx hxy.symm)
  subst y
  have hleader :
      (g.physical x).leader = false := by
    cases hl : (g.physical x).leader with
    | false =>
        rfl
    | true =>
        have hkill :=
          hlineage.2.2.2.2.1
            g x hpsi hself hwf hl
            (lemma9Tag i) hx
            (ring.rightNeighbor x)
        exact
          False.elim
            (hkill hy)
  have hhits :
      ((ghostStep ring g x).physical
        (ring.rightNeighbor x)).hits.val = 0 :=
    hlineage.2.2.2.2.2.2.1
      g x hpsi hself hwf hleader
      (lemma9Tag i) hx hy
  have httl :
      ((ghostStep ring g x).physical
        (ring.rightNeighbor x)).signalR.val ≤
        (g.physical x).signalR.val :=
    hlineage.2.2.2.2.2.1
      g x hpsi hself hwf
      x (ring.rightNeighbor x)
      (lemma9Tag i) hx hy
  dsimp only
  constructor
  · simp [lotteryStep, hhits]
  · have hw :
        (lotteryStep psi s false).wins =
          s.wins := by
      simp [lotteryStep]
    rw [hw]
    exact Nat.add_le_add_left httl _

private theorem lineage_H_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (x y i : Fin n)
    (hwf : LineageWellFormed g)
    (hnext : ∀ z : Fin n, 0 < g.nextArm z)
    (hx : g.owner x = some (lemma9Tag i))
    (hy :
      (ghostStep ring g (ring.leftNeighbor x)).owner y =
        some (lemma9Tag i))
    (s : LotteryState)
    (hsync : s.headRun = (g.physical x).hits.val) :
    let s' := lotteryStep psi s true
    s'.headRun =
        ((ghostStep ring g
          (ring.leftNeighbor x)).physical y).hits.val ∧
      s'.wins +
          ((ghostStep ring g
            (ring.leftNeighbor x)).physical y).signalR.val ≤
        s.wins + (g.physical x).signalR.val := by
  let e := ring.leftNeighbor x
  have hrx :
      ring.rightNeighbor e = x := by
    dsimp [e]
    exact rightNeighbor_leftNeighbor_lineage ring x
  have hself :
      ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_lineage hn3 ring e
  have hyx : y = x := by
    by_cases hye : y = e
    · subst y
      rw [ghostStep_initiator_owner_none] at hy
      contradiction
    by_cases hyr : y = ring.rightNeighbor e
    · exact hyr.trans hrx
    · have hold :
          g.owner y = some (lemma9Tag i) := by
        rw [← ghostStep_owner_other
          ring g e y hye hyr]
        exact hy
      have hxy :=
        hwf.2.1 x y (lemma9Tag i)
          hx hold
      have hyr' :
          y = ring.rightNeighbor e := by
        exact hxy.symm.trans hrx.symm
      exact False.elim (hyr hyr')
  subst y
  have hyresp :
      (ghostStep ring g e).owner
          (ring.rightNeighbor e) =
        some (lemma9Tag i) := by
    simpa [hrx] using hy
  have hwin :=
    responder_winner_of_some
      ring g e hself
      (lemma9Tag i) hyresp
  have hright :
      ¬ (g.physical (ring.rightNeighbor e)).signalR.val ≤
          armedTTL g e := by
    intro hcmp
    have hw := hwin
    rw [winnerOwner, if_pos hcmp] at hw
    by_cases hl :
        (g.physical e).leader = true
    · have hf :
          freshTag g e = lemma9Tag i := by
        simpa [armedOwner, hl] using hw
      exact
        (arm0_ne_fresh_lineage
          g i e hnext)
          hf.symm
    · have he :
          g.owner e = some (lemma9Tag i) := by
        simpa [armedOwner, hl] using hw
      have hxe :=
        hwf.2.1 x e (lemma9Tag i)
          hx he
      have hleft :
          e ≠ x := by
        dsimp [e]
        exact
          leftNeighbor_ne_self_lineage
            hn3 ring x
      exact hleft hxe.symm
  have hpos :=
    signal_pos_of_owner_lineage
      g x (lemma9Tag i) hwf hx
  have hd :=
    determineModeSignalProjection
      hpsi (g.physical e)
        (g.physical
          (ring.rightNeighbor e))
  dsimp only at hd
  have hrightCase :
      armedSignalVal (g.physical e) <
          (g.physical
            (ring.rightNeighbor e)).signalR.val ∧
        (PPL.determineMode
          (g.physical e)
          (g.physical
            (ring.rightNeighbor e))).2.signalR.val =
          (if bumpedHitsVal
              (g.physical
                (ring.rightNeighbor e)) = psi then
            (g.physical
              (ring.rightNeighbor e)).signalR.val - 1
          else
            (g.physical
              (ring.rightNeighbor e)).signalR.val) ∧
        (PPL.determineMode
          (g.physical e)
          (g.physical
            (ring.rightNeighbor e))).2.hits.val =
          (if bumpedHitsVal
              (g.physical
                (ring.rightNeighbor e)) = psi then
            0
          else
            bumpedHitsVal
              (g.physical
                (ring.rightNeighbor e))) := by
    rcases hd.2.2 with hz | hl | hr
    · have hz0 :
          (g.physical
            (ring.rightNeighbor e)).signalR.val = 0 :=
        hz.2.1
      rw [hrx] at hz0
      omega
    · have hle :
          (g.physical
            (ring.rightNeighbor e)).signalR.val ≤
              armedTTL g e := by
        simpa [armedTTL, armedSignalVal]
          using hl.2.1
      exact False.elim (hright hle)
    · exact hr
  have hp :=
    ghostStep_responder_projection_lineage
      hpsi ring g e hself
  dsimp only at hp
  have hsigPair :
      ((ghostStep ring g e).physical x).signalR.val =
        (PPL.determineMode
          (g.physical e)
          (g.physical
            (ring.rightNeighbor e))).2.signalR.val := by
    have hv := congrArg Fin.val hp.1
    simpa [hrx] using hv
  have hhitsPair :
      ((ghostStep ring g e).physical x).hits.val =
        (PPL.determineMode
          (g.physical e)
          (g.physical
            (ring.rightNeighbor e))).2.hits.val := by
    have hv := congrArg Fin.val hp.2
    simpa [hrx] using hv
  have hsig :
      ((ghostStep ring g e).physical x).signalR.val =
        (if bumpedHitsVal (g.physical x) = psi then
          (g.physical x).signalR.val - 1
        else
          (g.physical x).signalR.val) := by
    rw [hsigPair]
    simpa only [hrx] using hrightCase.2.1
  have hhits :
      ((ghostStep ring g e).physical x).hits.val =
        (if bumpedHitsVal (g.physical x) = psi then
          0
        else
          bumpedHitsVal (g.physical x)) := by
    rw [hhitsPair]
    simpa only [hrx] using hrightCase.2.2
  let s' := lotteryStep psi s true
  by_cases hwinp : psi ≤ s.headRun + 1
  · have hbump :
        bumpedHitsVal (g.physical x) = psi := by
      apply
        (bumpedHits_eq_psi_iff_lineage
          (g.physical x)).2
      simpa [hsync] using hwinp
    have hsig' :
        ((ghostStep ring g e).physical x).signalR.val =
          (g.physical x).signalR.val - 1 := by
      simpa [hbump] using hsig
    have hhits' :
        ((ghostStep ring g e).physical x).hits.val = 0 := by
      simpa [hbump] using hhits
    have hshead : s'.headRun = 0 := by
      simp [s', lotteryStep, hwinp]
    have hswins : s'.wins = s.wins + 1 := by
      simp [s', lotteryStep, hwinp]
    dsimp only
    constructor
    · rw [hshead, hhits']
    · rw [hswins, hsig']
      omega
  · have hbumpne :
        bumpedHitsVal (g.physical x) ≠ psi := by
      intro hb
      have hb' :=
        (bumpedHits_eq_psi_iff_lineage
          (g.physical x)).1 hb
      apply hwinp
      simpa [hsync] using hb'
    have hlt :
        (g.physical x).hits.val + 1 < psi := by
      omega
    have hbump :
        bumpedHitsVal (g.physical x) =
          (g.physical x).hits.val + 1 := by
      unfold bumpedHitsVal
      exact Nat.min_eq_left (Nat.le_of_lt hlt)
    have hsig' :
        ((ghostStep ring g e).physical x).signalR.val =
          (g.physical x).signalR.val := by
      simpa [hbumpne] using hsig
    have hhits' :
        ((ghostStep ring g e).physical x).hits.val =
          (g.physical x).hits.val + 1 := by
      calc
        ((ghostStep ring g e).physical x).hits.val =
            bumpedHitsVal (g.physical x) := by
          rw [hhits, if_neg hbumpne]
        _ = (g.physical x).hits.val + 1 := hbump
    have hshead :
        s'.headRun = s.headRun + 1 := by
      simp [s', lotteryStep, hwinp]
    have hswins :
        s'.wins = s.wins := by
      simp [s', lotteryStep, hwinp]
    dsimp only
    constructor
    · rw [hshead, hhits', hsync]
    · rw [hswins, hsig']
      exact Nat.le_refl _

private theorem lineage_other_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (g : GhostConfig n psi kappa)
    (e x y i : Fin n)
    (hwf : LineageWellFormed g)
    (hnext : ∀ z : Fin n, 0 < g.nextArm z)
    (hx : g.owner x = some (lemma9Tag i))
    (hy :
      (ghostStep ring g e).owner y =
        some (lemma9Tag i))
    (hT : e ≠ x)
    (hH : e ≠ ring.leftNeighbor x)
    (s : LotteryState)
    (hsync : s.headRun = (g.physical x).hits.val) :
    s.headRun =
        ((ghostStep ring g e).physical y).hits.val ∧
      s.wins +
          ((ghostStep ring g e).physical y).signalR.val ≤
        s.wins + (g.physical x).signalR.val := by
  have hself :=
    rightNeighbor_ne_self_lineage hn3 ring e
  have hxr :
      x ≠ ring.rightNeighbor e := by
    intro hx
    have hl :=
      congrArg
        (fun z => ring.leftNeighbor z) hx
    rw [leftNeighbor_rightNeighbor_lineage ring e] at hl
    exact hH hl.symm
  have hyx : y = x := by
    by_cases hye : y = e
    · subst y
      rw [ghostStep_initiator_owner_none] at hy
      contradiction
    by_cases hyr : y = ring.rightNeighbor e
    · subst y
      have hwin :=
        responder_winner_of_some
          ring g e hself
          (lemma9Tag i) hy
      rcases
          winnerOwner_some_cases
            g e (ring.rightNeighbor e)
            (lemma9Tag i) hwin with
        hnew | hold
      · exact False.elim
          ((arm0_ne_fresh_lineage
            g i e hnext) hnew.2)
      · rcases hold with he | hr
        · have hxe :=
            hwf.2.1 x e (lemma9Tag i)
              hx he
          exact False.elim (hT hxe.symm)
        · have hxr' :=
            hwf.2.1 x (ring.rightNeighbor e)
              (lemma9Tag i) hx hr
          exact False.elim (hxr hxr')
    · have hold :
          g.owner y = some (lemma9Tag i) := by
        rw [← ghostStep_owner_other
          ring g e y hye hyr]
        exact hy
      exact
        (hwf.2.1 x y (lemma9Tag i)
          hx hold).symm
  subst y
  have haway :=
    step_signal_hits_away
      ring g.physical e x (Ne.symm hT) hxr
  have hsig :
      ((ghostStep ring g e).physical x).signalR =
        (g.physical x).signalR := by
    change
      (step ring g.physical e x).signalR =
        (g.physical x).signalR
    exact haway.1
  have hhits :
      ((ghostStep ring g e).physical x).hits =
        (g.physical x).hits := by
    change
      (step ring g.physical e x).hits =
        (g.physical x).hits
    exact haway.2
  constructor
  · rw [congrArg Fin.val hhits]
    exact hsync
  · rw [congrArg Fin.val hsig]
    exact Nat.le_refl _

private theorem lineage_one_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (g : GhostConfig n psi kappa)
    (e x y i : Fin n)
    (hwf : LineageWellFormed g)
    (hnext : ∀ z : Fin n, 0 < g.nextArm z)
    (hx : g.owner x = some (lemma9Tag i))
    (hy :
      (ghostStep ring g e).owner y =
        some (lemma9Tag i))
    (s : LotteryState)
    (hsync : s.headRun = (g.physical x).hits.val) :
    let s' :=
      lineageLotteryAdvance psi s
        (incidentBit ring x e)
    s'.headRun =
        ((ghostStep ring g e).physical y).hits.val ∧
      s'.wins +
          ((ghostStep ring g e).physical y).signalR.val ≤
        s.wins + (g.physical x).signalR.val := by
  by_cases hT : e = x
  · subst e
    have h :=
      lineage_T_step
        hn3 hpsi ring hlineage
        g x y i hwf hx hy s hsync
    have hxl :
        x ≠ ring.leftNeighbor x := by
      intro heq
      exact
        (leftNeighbor_ne_self_lineage hn3 ring x)
          heq.symm
    simpa [lineageLotteryAdvance, incidentBit, hxl]
      using h
  · by_cases hH : e = ring.leftNeighbor x
    · subst e
      have h :=
        lineage_H_step
          hn3 hpsi ring g x y i
          hwf hnext hx hy s hsync
      simp [lineageLotteryAdvance, incidentBit] at h ⊢
      exact h
    · have h :=
        lineage_other_step
          hn3 ring g e x y i
          hwf hnext hx hy
          hT hH s hsync
      have hib :
          incidentBit ring x e = none := by
        simp [incidentBit, hH, hT]
      simpa [lineageLotteryAdvance, hib] using h

private theorem stoppedBits_length_eq_hitsAux_lineage
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (pre word : DetSchedule n) :
    (stoppedEncounterBitsAux
      ring host stop pre word).length =
      stoppedPredictableHostHitsAux
        ring host stop pre word := by
  induction word generalizing pre with
  | nil =>
      rfl
  | cons e rest ih =>
      cases hs : stop pre with
      | true =>
          simp [stoppedEncounterBitsAux,
            stoppedPredictableHostHitsAux, hs]
      | false =>
          let x := host pre
          by_cases hH :
              e = ring.leftNeighbor x
          · have hi :
                incidentBit ring x e = some true := by
              unfold incidentBit
              rw [if_pos hH]
            have hil :
                incidentLetter ring x e = true := by
              simp [incidentLetter, twoEdgeLetter, hH]
            simp [stoppedEncounterBitsAux,
              stoppedPredictableHostHitsAux,
              hs, x, hi, hil,
              ih (pre := pre ++ [e])]
            <;> omega
          · by_cases hT : e = x
            · have hi :
                  incidentBit ring x e = some false := by
                unfold incidentBit
                rw [if_neg hH, if_pos hT]
              have hil :
                  incidentLetter ring x e = true := by
                simp [incidentLetter, twoEdgeLetter, hT]
              simp [stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs, x, hi, hil,
                ih (pre := pre ++ [e])]
              <;> omega
            · have hi :
                  incidentBit ring x e = none := by
                simp [incidentBit, hH, hT]
              have hil :
                  incidentLetter ring x e = false := by
                simp [incidentLetter, twoEdgeLetter,
                  hH, hT]
              simp [stoppedEncounterBitsAux,
                stoppedPredictableHostHitsAux,
                hs, x, hi, hil,
                ih (pre := pre ++ [e])]

private theorem stoppedBits_length_eq_hits_lineage
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (word : DetSchedule n) :
    (stoppedEncounterBits
      ring host stop word).length =
      stoppedPredictableHostHits
        ring host stop word := by
  exact
    stoppedBits_length_eq_hitsAux_lineage
      ring host stop [] word

private theorem lotteryStep_wins_mono_lineage
    (psi : Nat) (s : LotteryState)
    (b : Bool) :
    s.wins ≤ (lotteryStep psi s b).wins := by
  cases b with
  | false =>
      simp [lotteryStep]
  | true =>
      by_cases h : psi ≤ s.headRun + 1
      · simp [lotteryStep, h]
      · simp [lotteryStep, h]

private theorem lotteryRun_wins_mono_lineage
    (psi : Nat) (s : LotteryState)
    (word : List Bool) :
    s.wins ≤ (lotteryRun psi s word).wins := by
  induction word generalizing s with
  | nil =>
      exact Nat.le_refl _
  | cons b rest ih =>
      exact
        Nat.le_trans
          (lotteryStep_wins_mono_lineage
            psi s b)
          (ih (lotteryStep psi s b))

private theorem lotteryRun_append_lineage
    (psi : Nat) (s : LotteryState)
    (u v : List Bool) :
    lotteryRun psi s (u ++ v) =
      lotteryRun psi
        (lotteryRun psi s u) v := by
  induction u generalizing s with
  | nil =>
      rfl
  | cons b rest ih =>
      simp only [List.cons_append, lotteryRun]
      exact ih (lotteryStep psi s b)

private theorem lotteryRun_take_wins_le_lineage
    (psi : Nat) (s : LotteryState)
    (bits : List Bool) (E : Nat) :
    (lotteryRun psi s (bits.take E)).wins ≤
      (lotteryRun psi s bits).wins := by
  calc
    (lotteryRun psi s (bits.take E)).wins ≤
        (lotteryRun psi
          (lotteryRun psi s (bits.take E))
          (bits.drop E)).wins :=
      lotteryRun_wins_mono_lineage
        psi
        (lotteryRun psi s (bits.take E))
        (bits.drop E)
    _ = (lotteryRun psi s
          (bits.take E ++ bits.drop E)).wins := by
      rw [lotteryRun_append_lineage]
    _ = (lotteryRun psi s bits).wins := by
      rw [List.take_append_drop]

private theorem lineage_run_budget_aux
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (pre word : DetSchedule n)
    (s : LotteryState)
    (hstop :
      stopReachedAux
        (lemma9Stop ring C i) pre word = false)
    (hsync :
      s.headRun =
        ((ghostRun ring (initialGhost C) pre).physical
          (lineageHost ring C i pre)).hits.val) :
    let bits :=
      stoppedEncounterBitsAux
        ring (lineageHost ring C i)
        (lemma9Stop ring C i) pre word
    let g0 :=
      ghostRun ring (initialGhost C) pre
    let gf :=
      ghostRun ring (initialGhost C)
        (pre ++ word)
    let xf :=
      lineageHost ring C i (pre ++ word)
    (lotteryRun psi s bits).headRun =
        (gf.physical xf).hits.val ∧
      (lotteryRun psi s bits).wins +
          (gf.physical xf).signalR.val ≤
        s.wins +
          (g0.physical
            (lineageHost ring C i pre)).signalR.val := by
  induction word generalizing pre s with
  | nil =>
      dsimp only
      simp only [stoppedEncounterBitsAux, lotteryRun,
        List.append_nil]
      exact
        ⟨hsync,
          Nat.le_refl
            (s.wins +
              ((ghostRun ring (initialGhost C) pre).physical
                (lineageHost ring C i pre)).signalR.val)⟩
  | cons e rest ih =>
      let g :=
        ghostRun ring (initialGhost C) pre
      let x :=
        lineageHost ring C i pre
      let pre' := pre ++ [e]
      let y :=
        lineageHost ring C i pre'
      have hs0 :=
        stop_false_of_stopReachedAux_false_lineage
          (lemma9Stop ring C i)
          pre (e :: rest) hstop
      have htail :=
        stopReachedAux_tail_false_lineage
          (lemma9Stop ring C i)
          pre e rest hstop
      have hs1 :=
        stop_false_of_stopReachedAux_false_lineage
          (lemma9Stop ring C i)
          pre' rest htail
      have hx :
          g.owner x = some (lemma9Tag i) := by
        dsimp [g, x]
        exact
          lineageHost_owner
            ring C i pre hs0
      have hy0 :
          (ghostRun ring (initialGhost C) pre').owner y =
            some (lemma9Tag i) := by
        dsimp [y]
        exact
          lineageHost_owner
            ring C i pre' hs1
      have hgstep :
          ghostRun ring (initialGhost C) pre' =
            ghostStep ring g e := by
        dsimp [pre', g]
        rw [ghostRun_append_lineage]
        rfl
      have hy :
          (ghostStep ring g e).owner y =
            some (lemma9Tag i) := by
        rw [← hgstep]
        exact hy0
      have hinv :=
        ghostRun_invariants_lineage
          hn3 hpsi ring
          (initialGhost C) pre
          (initialGhost_wellFormed C)
          (by
            intro z
            simp [initialGhost])
      have hwf :
          LineageWellFormed g := by
        simpa [g] using hinv.1
      have hnext :
          ∀ z : Fin n, 0 < g.nextArm z := by
        simpa [g] using hinv.2
      let s' :=
        lineageLotteryAdvance psi s
          (incidentBit ring x e)
      have hlocal :
          s'.headRun =
              ((ghostStep ring g e).physical y).hits.val ∧
            s'.wins +
                ((ghostStep ring g e).physical y).signalR.val ≤
              s.wins +
                (g.physical x).signalR.val := by
        dsimp [s']
        exact
          lineage_one_step
            hn3 hpsi ring hlineage
            g e x y i hwf hnext
            hx hy s
            (by simpa [g, x] using hsync)
      have hsync' :
          s'.headRun =
            ((ghostRun ring (initialGhost C) pre').physical
              (lineageHost ring C i pre')).hits.val := by
        rw [hgstep]
        simpa [y] using hlocal.1
      have hrec :=
        ih (pre := pre') (s := s')
          htail hsync'
      let tailBits :=
        stoppedEncounterBitsAux
          ring (lineageHost ring C i)
          (lemma9Stop ring C i) pre' rest
      have hbits :
          stoppedEncounterBitsAux
              ring (lineageHost ring C i)
              (lemma9Stop ring C i)
              pre (e :: rest) =
            match incidentBit ring x e with
            | none => tailBits
            | some b => b :: tailBits := by
        cases hb : incidentBit ring x e with
        | none =>
            simp [stoppedEncounterBitsAux, hs0,
              x, pre', tailBits, hb]
        | some b =>
            simp [stoppedEncounterBitsAux, hs0,
              x, pre', tailBits, hb]
      have hrun :
          lotteryRun psi s
              (stoppedEncounterBitsAux
                ring (lineageHost ring C i)
                (lemma9Stop ring C i)
                pre (e :: rest)) =
            lotteryRun psi s' tailBits := by
        rw [hbits]
        cases hb : incidentBit ring x e with
        | none =>
            simp [s', lineageLotteryAdvance, hb]
        | some b =>
            simp [s', lineageLotteryAdvance,
              hb, lotteryRun]
      dsimp only at hrec ⊢
      have hprefix :
          pre' ++ rest =
            pre ++ (e :: rest) := by
        dsimp [pre']
        simp [List.append_assoc]
      rw [hrun]
      have hhead := hrec.1
      rw [hprefix] at hhead
      constructor
      · exact hhead
      · have hbudget := hrec.2
        rw [hprefix] at hbudget
        have hlocal' := hlocal.2
        have hmid :
            s'.wins +
                ((ghostRun ring (initialGhost C) pre').physical
                  (lineageHost ring C i pre')).signalR.val ≤
              s.wins +
                ((ghostRun ring (initialGhost C) pre).physical
                  (lineageHost ring C i pre)).signalR.val := by
          rw [hgstep]
          simpa [g, x, y] using hlocal'
        have htotal :=
          Nat.le_trans hbudget hmid
        simpa [tailBits] using htotal

private theorem lineage_full_wins_le_initial_ttl
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (word : DetSchedule n)
    (hsignal : 0 < (C i).signalR.val)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (hstop :
      stopReached
        (lemma9Stop ring C i) word = false) :
    (lotteryRun psi
      (lotteryOffset (C i).hits.val)
      (stoppedEncounterBits
        ring (lineageHost ring C i)
        (lemma9Stop ring C i) word)).wins ≤
      (C i).signalR.val := by
  have hhost0 :=
    lineageHost_nil_eq_origin
      ring C i hsignal
  have hsync :
      (lotteryOffset (C i).hits.val).headRun =
        ((ghostRun ring (initialGhost C) []).physical
          (lineageHost ring C i [])).hits.val := by
    change
      (C i).hits.val =
        (C (lineageHost ring C i [])).hits.val
    rw [hhost0]
  have haux :=
    lineage_run_budget_aux
      hn3 hpsi ring C i hlineage
      [] word
      (lotteryOffset (C i).hits.val)
      (by simpa [stopReached] using hstop)
      hsync
  dsimp only at haux
  have hb := haux.2
  have hstart :
      ((ghostRun ring (initialGhost C) []).physical
        (lineageHost ring C i [])).signalR.val =
          (C i).signalR.val := by
    change
      (C (lineageHost ring C i [])).signalR.val =
        (C i).signalR.val
    rw [hhost0]
  rw [hstart] at hb
  have hb' :
      (lotteryRun psi
        (lotteryOffset (C i).hits.val)
        (stoppedEncounterBits
          ring (lineageHost ring C i)
          (lemma9Stop ring C i) word)).wins +
          ((ghostRun ring (initialGhost C) word).physical
            (lineageHost ring C i word)).signalR.val ≤
        (C i).signalR.val := by
    simpa [stoppedEncounterBits, lotteryOffset] using hb
  omega

private theorem countP_mono_lineage
    {A : Type}
    (xs : List A)
    (p q : A → Bool)
    (hpq : ∀ x, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqt := hpq x hp
          simp [hp, hqt]
          omega

private theorem countP_or_le_add_lineage
    {A : Type}
    (xs : List A)
    (p q : A → Bool) :
    xs.countP (fun x => p x || q x) ≤
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons, List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega

theorem lemma9LineageFailureSplit :
    Lemma9LineageFailureSplit := by
  intro n psi kappa c
  intro hn3 hpsi hkappa
  intro ring C i
  intro hsignal hlineage
  let host : List (Fin n) → Fin n :=
    lineageHost ring C i
  refine ⟨host, ?_, ?_⟩
  · intro pre hstop
    dsimp [host]
    exact
      lineageHost_owner
        ring C i pre hstop
  · let T := lemma9T n psi c
    let E := lemma9E psi c
    let stop := lemma9Stop ring C i
    let p : DetSchedule n → Bool :=
      fun word =>
        tagAliveB
          (ghostRun ring (initialGhost C) word)
          (lemma9Tag i)
    let q : DetSchedule n → Bool :=
      fun word =>
        decide
          (stopReached stop word = false ∧
            stoppedPredictableHostHits
              ring host stop word < E)
    let r : DetSchedule n → Bool :=
      fun word =>
        let bits :=
          stoppedEncounterBits ring host stop word
        decide
          (stopReached stop word = false ∧
            E ≤ bits.length ∧
            (lotteryRun psi
              (lotteryOffset (C i).hits.val)
              (bits.take E)).wins ≤
                lotteryTarget psi c)
    have hpoint :
        ∀ word : DetSchedule n,
          p word = true →
          (q word || r word) = true := by
      intro word hp
      have hstop :
          stopReached stop word = false := by
        dsimp [stop]
        exact
          stopReached_false_of_final_alive_lineage
            hn3 hpsi ring C i word
            (by simpa [p] using hp)
      have hfull :
          (lotteryRun psi
            (lotteryOffset (C i).hits.val)
            (stoppedEncounterBits
              ring host stop word)).wins ≤
            (C i).signalR.val := by
        dsimp [host, stop]
        exact
          lineage_full_wins_le_initial_ttl
            hn3 hpsi ring C i word
            hsignal hlineage hstop
      have htarget :
          (C i).signalR.val ≤
            lotteryTarget psi c := by
        have hlt := (C i).signalR.isLt
        unfold lotteryTarget
        omega
      by_cases hlow :
          stoppedPredictableHostHits
            ring host stop word < E
      · have hq : q word = true := by
          dsimp [q]
          simp only [decide_eq_true_eq]
          exact ⟨hstop, hlow⟩
        simp [hq]
      · have hge :
            E ≤ stoppedPredictableHostHits
              ring host stop word := by
          omega
        let bits :=
          stoppedEncounterBits
            ring host stop word
        have hlen :
            E ≤ bits.length := by
          have hlenEq :=
            stoppedBits_length_eq_hits_lineage
              ring host stop word
          dsimp [bits]
          rw [hlenEq]
          exact hge
        have htake :=
          lotteryRun_take_wins_le_lineage
            psi
            (lotteryOffset (C i).hits.val)
            bits E
        have hwins :
            (lotteryRun psi
              (lotteryOffset (C i).hits.val)
              (bits.take E)).wins ≤
                lotteryTarget psi c := by
          exact
            Nat.le_trans htake
              (Nat.le_trans
                (by simpa [bits] using hfull)
                htarget)
        have hr : r word = true := by
          dsimp [r]
          simp only [decide_eq_true_eq]
          exact ⟨hstop, hlen, hwins⟩
        simp [hr]
    have hcount :
        (allSchedules n T).countP p ≤
          (allSchedules n T).countP q +
            (allSchedules n T).countP r := by
      calc
        (allSchedules n T).countP p ≤
            (allSchedules n T).countP
              (fun word => q word || r word) :=
          countP_mono_lineage
            (allSchedules n T) p
            (fun word => q word || r word)
            hpoint
        _ ≤
            (allSchedules n T).countP q +
              (allSchedules n T).countP r :=
          countP_or_le_add_lineage
            (allSchedules n T) q r
    unfold lemma9FailureCount
    dsimp
    change
      (allSchedules n T).countP p ≤
        (allSchedules n T).countP q +
          (allSchedules n T).countP r
    exact hcount

#print axioms PPL.Modes.Lemma9.lemma9LineageFailureSplit

end PPL.Modes.Lemma9

