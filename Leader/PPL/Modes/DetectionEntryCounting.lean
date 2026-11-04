import Leader.PPL.Modes.DetectionEntrySplit


namespace PPL.Modes.Lemma6


set_option autoImplicit false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


private theorem allSchedules_add_local (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap (fun pre =>
        (allSchedules n b).map (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules, List.flatMap_assoc, List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]


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


private theorem reachesAux_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    reachesAux ring C (u ++ v) =
      (reachesAux ring C u ||
        reachesAux ring (runPPL ring C u) v) := by
  induction u generalizing C with
  | nil =>
      cases v with
      | nil =>
          simp [reachesAux, runPPL, runPopulationSchedule]
      | cons e rest =>
          cases hgood : lemma6GoodB C <;>
            simp [reachesAux, runPPL, runPopulationSchedule, hgood]
  | cons e rest ih =>
      simp only [List.cons_append, reachesAux]
      rw [ih]
      simp only [runPPL, runPopulationSchedule]
      cases lemma6GoodB C <;>
        cases reachesAux ring (pplStep ring C e) rest <;>
        cases reachesAux ring
          (runPPL ring (pplStep ring C e) rest) v <;>
        rfl


private theorem reachesAux_false_endpoint_good_false
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h : reachesAux ring C word = false) :
    lemma6GoodB (runPPL ring C word) = false := by
  have happ := reachesAux_append ring C word []
  simpa [h, reachesAux] using happ.symm


private theorem reachesAux_false_endpoint_leaderless
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (h : reachesAux ring C word = false) :
    leaderPresent (runPPL ring C word) = false := by
  have hgood :=
    reachesAux_false_endpoint_good_false ring C word h
  unfold lemma6GoodB at hgood
  cases hl : leaderPresent (runPPL ring C word)
  · rfl
  · simp [hl] at hgood


private theorem countP_mono_local
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
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega


private theorem sum_map_le_local
    {A : Type}
    (xs : List A)
    (f g : A → Nat)
    (hfg : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (hfg x (by simp))
        (ih (fun y hy => hfg y (by simp [hy])))


private theorem scaled_sum_le_countP_mul_add_length_mul
    {A : Type}
    (xs : List A)
    (p : A → Bool)
    (f : A → Nat)
    (scale u v : Nat)
    (hpoint :
      ∀ x, x ∈ xs →
        scale * f x ≤
          (if p x then u else 0) + v) :
    scale * (xs.map f).sum ≤
      xs.countP p * u + xs.length * v := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx := hpoint x (by simp)
      have ht :=
        ih (fun y hy => hpoint y (by simp [hy]))
      rw [List.map_cons, List.sum_cons, List.countP_cons,
        List.length_cons, Nat.mul_add, Nat.succ_mul]
      cases hp : p x <;>
        simp [hp, Nat.add_mul] at hx ⊢ <;>
        omega


private def childFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n T).map (fun suf => pre ++ suf)).countP
    (fun word => !(reachesAux ring C word))


private theorem childFailureCount_zero_of_prefix_good
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat)
    (pre : DetSchedule n)
    (hpre : reachesAux ring C pre = true) :
    childFailureCount ring C T pre = 0 := by
  unfold childFailureCount
  apply List.countP_eq_zero.mpr
  intro word hword hbad
  rw [List.mem_map] at hword
  obtain ⟨suf, hsuf, rfl⟩ := hword
  have happ := reachesAux_append ring C pre suf
  rw [hpre] at happ
  simp only [Bool.true_or] at happ
  rw [happ] at hbad
  contradiction


private theorem childFailureCount_le_full
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat)
    (pre : DetSchedule n) :
    childFailureCount ring C T pre ≤ n ^ T := by
  unfold childFailureCount
  calc
    ((allSchedules n T).map
        (fun suf => pre ++ suf)).countP
        (fun word => !(reachesAux ring C word)) ≤
      ((allSchedules n T).map
        (fun suf => pre ++ suf)).length :=
      List.countP_le_length
    _ = (allSchedules n T).length := by
      rw [List.length_map]
    _ = n ^ T :=
      allSchedules_length n T


private theorem childFailureCount_eq_clock
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat)
    (pre : DetSchedule n)
    (hpre : reachesAux ring C pre = false) :
    childFailureCount ring C (lemma9T n psi c) pre =
      lemma6ClockPhaseFailureCount
        ring (runPPL ring C pre) c := by
  unfold childFailureCount lemma6ClockPhaseFailureCount
  rw [List.countP_map]
  simp only [Function.comp_def]
  apply congrArg (fun p => (allSchedules n (lemma9T n psi c)).countP p)
  funext suf
  rw [reachesAux_append, hpre, Bool.false_or]


private theorem lemma6FailureCount_eq_child_sum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) :
    lemma6FailureCount ring C c =
      ((allSchedules n (lemma9T n psi c)).map
        (childFailureCount ring C (lemma9T n psi c))).sum := by
  unfold lemma6FailureCount lemma6Horizon childFailureCount
  rw [show
      2 * lemma9T n psi c =
        lemma9T n psi c + lemma9T n psi c by omega]
  rw [allSchedules_add_local, List.countP_flatMap]
  rfl


theorem lemma6TwoBlockBind :
    Lemma6TwoBlockBind := by
  intro n psi kappa c A B ring C hsignal hclock


  let T := lemma9T n psi c
  let badPre : DetSchedule n → Bool :=
    fun pre =>
      decide
        (reachesAux ring C pre = false ∧
          signalFreeB (runPPL ring C pre) = false)
  let child : DetSchedule n → Nat :=
    childFailureCount ring C T


  have hpoint :
      ∀ pre, pre ∈ allSchedules n T →
        n * child pre ≤
          (if badPre pre then n * n ^ T else 0) +
            B * n ^ T := by
    intro pre hmem
    by_cases hpre : reachesAux ring C pre = true
    · have hz :
          child pre = 0 := by
        exact
          childFailureCount_zero_of_prefix_good
            ring C T pre hpre
      rw [hz]
      simp
    · have hpreFalse :
          reachesAux ring C pre = false := by
        cases h : reachesAux ring C pre
        · rfl
        · contradiction
      by_cases hfree :
          signalFreeB (runPPL ring C pre) = false
      · have hbad : badPre pre = true := by
          simp [badPre, hpreFalse, hfree]
        simp only [hbad, if_pos rfl]
        have hfull :=
          childFailureCount_le_full ring C T pre
        have hm :
            n * child pre ≤ n * n ^ T := by
          dsimp [child]
          exact Nat.mul_le_mul_left n hfull
        simp only [↓reduceIte]
        omega
      · have hfreeTrue :
          signalFreeB (runPPL ring C pre) = true := by
          cases hval : signalFreeB (runPPL ring C pre)
          · exact False.elim (hfree hval)
          · rfl
        have hbad : badPre pre = false := by
          simp [badPre, hpreFalse, hfreeTrue]
        simp [hbad]
        have hleader :=
          reachesAux_false_endpoint_leaderless
            ring C pre hpreFalse
        have hbound :=
          hclock (runPPL ring C pre) hleader hfreeTrue
        have heq :
            child pre =
              lemma6ClockPhaseFailureCount
                ring (runPPL ring C pre) c := by
          dsimp [child, T]
          exact
            childFailureCount_eq_clock
              ring C c pre hpreFalse
        rw [heq]
        simpa [T] using hbound


  have hsum :=
    scaled_sum_le_countP_mul_add_length_mul
      (allSchedules n T) badPre child
      n (n * n ^ T) (B * n ^ T) hpoint


  have hbadCount :
      (allSchedules n T).countP badPre =
        lemma6SignalPhaseFailureCount ring C c := by
    rfl


  have hlen :
      (allSchedules n T).length = n ^ T :=
    allSchedules_length n T


  rw [hbadCount, hlen] at hsum


  have hfirst :
      lemma6SignalPhaseFailureCount ring C c *
          (n * n ^ T) ≤
        (A * n ^ T) * n ^ T := by
    calc
      lemma6SignalPhaseFailureCount ring C c *
            (n * n ^ T) =
          (n * lemma6SignalPhaseFailureCount ring C c) *
            n ^ T := by
        ac_rfl
      _ ≤ (A * n ^ T) * n ^ T :=
        Nat.mul_le_mul_right (n ^ T) hsignal


  have htotal :
      n *
          ((allSchedules n T).map child).sum ≤
        (A + B) * n ^ (T + T) := by
    calc
      n * ((allSchedules n T).map child).sum ≤
          lemma6SignalPhaseFailureCount ring C c *
              (n * n ^ T) +
            n ^ T * (B * n ^ T) := hsum
      _ ≤
          (A * n ^ T) * n ^ T +
            n ^ T * (B * n ^ T) :=
        Nat.add_le_add hfirst (Nat.le_refl _)
      _ = (A + B) * n ^ (T + T) := by
        rw [Nat.pow_add, Nat.add_mul]
        ac_rfl


  unfold Lemma6TwoBlockBind at *
  rw [lemma6FailureCount_eq_child_sum ring C c]
  have hH :
      lemma6Horizon n psi c = T + T := by
    dsimp [T, lemma6Horizon]
    omega
  rw [hH]
  exact htotal


private theorem foldl_or_true
    (xs : List Bool) :
    xs.foldl (fun acc b => acc || b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons, Bool.true_or]
      exact ih


private theorem foldl_or_true_of_mem
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
        exact foldl_or_true xs
      · cases b
        · simp only [List.foldl_cons, Bool.false_or]
          exact ih ht
        · simp only [List.foldl_cons, Bool.false_or]
          exact foldl_or_true xs


private theorem tagAliveB_true_of_owner
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (tag : SignalTag n)
    (j : Fin n)
    (howner : g.owner j = some tag) :
    tagAliveB g tag = true := by
  unfold tagAliveB
  apply foldl_or_true_of_mem
  rw [List.mem_ofFn]
  refine ⟨j, ?_⟩
  simp [howner]


private def startTagAlivePred
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (word : DetSchedule n) : Bool :=
  if h : 0 < (C i).signalR.val then
    tagAliveB
      (ghostRun ring (initialGhost C) word)
      (lemma9Tag i)
  else
    false


private def anyPred {A : Type} :
    List (A → Bool) → A → Bool
  | [], _ => false
  | p :: ps, x => p x || anyPred ps x


private theorem anyPred_true_of_mem
    {A : Type}
    (ps : List (A → Bool))
    (p : A → Bool)
    (x : A)
    (hmem : p ∈ ps)
    (hp : p x = true) :
    anyPred ps x = true := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q qs ih =>
      rcases List.mem_cons.mp hmem with hq | hq
      · subst q
        simp [anyPred, hp]
      · have ht := ih hq
        simp [anyPred, ht]


private theorem countP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A → Bool) :
    xs.countP (fun x => p x || q x) ≤
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] at * <;>
        omega


private theorem countP_anyPred_le_sum
    {A : Type}
    (xs : List A)
    (ps : List (A → Bool)) :
    xs.countP (anyPred ps) ≤
      (ps.map (fun p => xs.countP p)).sum := by
  induction ps with
  | nil =>
      simp [anyPred]
  | cons p ps ih =>
      calc
        xs.countP (anyPred (p :: ps)) =
            xs.countP (fun x => p x || anyPred ps x) := by
          rfl
        _ ≤ xs.countP p + xs.countP (anyPred ps) :=
          countP_or_le_add xs p (anyPred ps)
        _ ≤ xs.countP p +
            (ps.map (fun q => xs.countP q)).sum :=
          Nat.add_le_add_left ih _
        _ =
            ((p :: ps).map (fun q => xs.countP q)).sum := by
          simp


private theorem sum_ofFn_le_local
    {n : Nat}
    (f g : Fin n → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add
        (hfg 0)
        (ih
          (fun i => f i.succ)
          (fun i => g i.succ)
          (fun i => hfg i.succ))


private theorem sum_ofFn_mul_left_local
    {n : Nat}
    (a : Nat)
    (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]


private theorem sum_ofFn_const_local
    (n a : Nat) :
    (List.ofFn (fun _ : Fin n => a)).sum =
      n * a := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega


private theorem signal_bad_has_surviving_start_tag
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hcoverage : Lemma6LeaderlessSignalCoverage)
    (hlineage :
      SignalLineageOwnership (psi := psi) (kappa := kappa) ring)
    (hbad :
      decide
        (reachesAux ring C word = false ∧
          signalFreeB (runPPL ring C word) = false) = true) :
    ∃ i : Fin n,
      startTagAlivePred ring C i word = true := by
  have hb :
      reachesAux ring C word = false ∧
        signalFreeB (runPPL ring C word) = false :=
    of_decide_eq_true hbad


  let start := initialGhost C
  let current := ghostRun ring start word


  have hnotGone :
      ¬ StartTagsGone start current := by
    intro hgone
    have hfree :=
      hcoverage hn3 hpsi ring C word
        hlineage hb.1
        (by
          simpa [start, current] using hgone)
    rw [hb.2] at hfree
    contradiction


  unfold StartTagsGone at hnotGone
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hnotGone
  obtain ⟨t, ht⟩ := Classical.not_forall.mp hi


  have hstart :
      start.owner i = some t := by
    apply Classical.byContradiction
    intro hne
    apply ht
    intro howner
    exact False.elim (hne howner)


  have hnotCurrent :
      ¬ ∀ j : Fin n, current.owner j ≠ some t := by
    intro hall
    apply ht
    intro _
    exact hall


  obtain ⟨j, hj⟩ :=
    Classical.not_forall.mp hnotCurrent


  have hcurrent :
      current.owner j = some t := by
    apply Classical.byContradiction
    intro hne
    exact hj hne


  have hpos :
      0 < (C i).signalR.val := by
    by_cases hp : 0 < (C i).signalR.val
    · exact hp
    · have hnone :
          start.owner i = none := by
        simp [start, initialGhost, hp]
      rw [hnone] at hstart
      contradiction


  have htag :
      t = lemma9Tag i := by
    have hs := hstart
    simp [start, initialGhost, hpos, lemma9Tag] at hs
    exact hs.symm


  have halive :
      tagAliveB
        (ghostRun ring (initialGhost C) word)
        (lemma9Tag i) = true := by
    subst t
    apply tagAliveB_true_of_owner
      (ghostRun ring (initialGhost C) word)
      (lemma9Tag i) j
    simpa [current, start] using hcurrent


  refine ⟨i, ?_⟩
  simp [startTagAlivePred, hpos, halive]


theorem lemma6SignalClearanceCount :
    Lemma6SignalClearanceCount := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring C
  intro hcoverage hlineage h9


  let T := lemma9T n psi c
  let words := allSchedules n T
  let bad : DetSchedule n → Bool :=
    fun word =>
      decide
        (reachesAux ring C word = false ∧
          signalFreeB (runPPL ring C word) = false)
  let sitePred : Fin n → DetSchedule n → Bool :=
    fun i word => startTagAlivePred ring C i word
  let preds : List (DetSchedule n → Bool) :=
    List.ofFn sitePred


  have hbadToAny :
      ∀ word, bad word = true →
        anyPred preds word = true := by
    intro word hbad
    obtain ⟨i, hi⟩ :=
      signal_bad_has_surviving_start_tag
        hn3 hpsi ring C word
        hcoverage hlineage
        (by simpa [bad] using hbad)
    apply anyPred_true_of_mem preds (sitePred i) word
    · dsimp [preds]
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · simpa [sitePred] using hi


  have hunion :
      lemma6SignalPhaseFailureCount ring C c ≤
        (List.ofFn (fun i : Fin n =>
          words.countP (sitePred i))).sum := by
    calc
      lemma6SignalPhaseFailureCount ring C c =
          words.countP bad := by
        rfl
      _ ≤ words.countP (anyPred preds) :=
        countP_mono_local words bad (anyPred preds) hbadToAny
      _ ≤
          (preds.map (fun p => words.countP p)).sum :=
        countP_anyPred_le_sum words preds
      _ =
          (List.ofFn (fun i : Fin n =>
            words.countP (sitePred i))).sum := by
        dsimp [preds]
        rw [List.map_ofFn]
        simp only [Function.comp_def]


  have hsite :
      ∀ i : Fin n,
        n * n * words.countP (sitePred i) ≤
          4 * n ^ T := by
    intro i
    by_cases hpos : 0 < (C i).signalR.val
    · have hi := h9 i hpos
      unfold Lemma9WordBound at hi
      simpa [words, sitePred, startTagAlivePred,
        T, hpos, lemma9FailureCount, lemma9Tag] using hi
    · have hz :
          words.countP (sitePred i) = 0 := by
        dsimp [sitePred]
        simp [startTagAlivePred, hpos]
      rw [hz]
      simp


  have hsum :
      (List.ofFn (fun i : Fin n =>
        n * n * words.countP (sitePred i))).sum ≤
      (List.ofFn (fun _ : Fin n =>
        4 * n ^ T)).sum :=
    sum_ofFn_le_local _ _ hsite


  have hscaledUnion :
      n * n * lemma6SignalPhaseFailureCount ring C c ≤
        n * (4 * n ^ T) := by
    calc
      n * n * lemma6SignalPhaseFailureCount ring C c ≤
          n * n *
            (List.ofFn (fun i : Fin n =>
              words.countP (sitePred i))).sum :=
        Nat.mul_le_mul_left (n * n) hunion
      _ =
          (List.ofFn (fun i : Fin n =>
            n * n * words.countP (sitePred i))).sum := by
        rw [sum_ofFn_mul_left_local]
      _ ≤
          (List.ofFn (fun _ : Fin n =>
            4 * n ^ T)).sum := hsum
      _ = n * (4 * n ^ T) :=
        sum_ofFn_const_local n (4 * n ^ T)


  have hnpos : 0 < n := by
    omega


  have hcancel :
      n * (n * lemma6SignalPhaseFailureCount ring C c) ≤
        n * (4 * n ^ T) := by
    simpa [Nat.mul_assoc] using hscaledUnion


  have hout :
      n * lemma6SignalPhaseFailureCount ring C c ≤
        4 * n ^ T :=
    Nat.le_of_mul_le_mul_left hcancel hnpos


  simpa [T] using hout


#print axioms allSchedules_add_local
#print axioms runPPL_append
#print axioms reachesAux_append
#print axioms reachesAux_false_endpoint_good_false
#print axioms reachesAux_false_endpoint_leaderless
#print axioms countP_mono_local
#print axioms sum_map_le_local
#print axioms scaled_sum_le_countP_mul_add_length_mul
#print axioms childFailureCount_zero_of_prefix_good
#print axioms childFailureCount_le_full
#print axioms childFailureCount_eq_clock
#print axioms lemma6FailureCount_eq_child_sum
#print axioms lemma6TwoBlockBind
#print axioms foldl_or_true
#print axioms foldl_or_true_of_mem
#print axioms tagAliveB_true_of_owner
#print axioms anyPred_true_of_mem
#print axioms countP_or_le_add
#print axioms countP_anyPred_le_sum
#print axioms sum_ofFn_le_local
#print axioms sum_ofFn_mul_left_local
#print axioms sum_ofFn_const_local
#print axioms signal_bad_has_surviving_start_tag
#print axioms lemma6SignalClearanceCount


end PPL.Modes.Lemma6


