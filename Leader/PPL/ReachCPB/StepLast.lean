import Leader.PPL.ReachCPB.ForcingCapped
import Leader.PPL.TransitionFacts

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Lemma 16 capped last sweep: one literal interaction

Truth audit on current main.

`Lemma16LastForcingCappedStepSpec` is TRUE.

Under `DistReadyCapped`, the input is leaderless, signal-free, every clock is
at `kappa`, and the cyclic successor-distance equation holds.  Therefore the
literal selected pair has this shape.

* DetermineMode keeps both clocks at the cap and writes Detect.
* Algorithm 2 line 6 is disabled because its temporary successor distance is
  exactly the responder distance.
* Line 8 is disabled because the responder is Detect.
* Line 9 is the only write to `last`: it clears the initiator when the
  responder is a border, otherwise it copies the responder's `last`.
* Both MoveToken passes and Algorithm 5 preserve `clock/mode/signalR/dist/last`
  after those writes, by the TransitionFacts / OtherFields projections.
* A later token comparison may create a leader.  That is the CPB branch,
  because AllLivePeaceful is already one-step closed.

The bounded-round residual below is only that literal pair-row projection.  It
has no base/front/sweep predicates and no schedule quantification.  Everything
from the pair row through LastClearedCapped progress is closed in this file.
-/

/-! ## Bool all-agent bridges -/

private def lastStepFoldlAndFalse
    (xs : List Bool) :
    xs.foldl (fun a b => a && b) false = false := by
  induction xs with
  | nil =>
      rfl
  | cons b xs ih =>
      simp only [List.foldl_cons]
      cases b <;> simpa using ih

private def lastStepFoldlAndTrueAllTrue
    (xs : List Bool)
    (h :
      xs.foldl (fun a b => a && b) true = true) :
    forall b, b ∈ xs -> b = true := by
  induction xs with
  | nil =>
      intro b hb
      simp at hb
  | cons a xs ih =>
      cases ha : a with
      | false =>
          have ht :
              xs.foldl (fun u v => u && v) false = false :=
            lastStepFoldlAndFalse xs
          have hf : False := by
            rw [List.foldl_cons, ha] at h
            simp only [Bool.true_and] at h
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

private def lastStepFoldlAndTrueOfAllTrue
    (xs : List Bool)
    (h : forall b, b ∈ xs -> b = true) :
    xs.foldl (fun a b => a && b) true = true := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      have ha : a = true :=
        h a (by simp)
      have ht :
          forall b, b ∈ xs -> b = true := by
        intro b hb
        exact h b (by simp [hb])
      simpa [List.foldl_cons, ha] using ih ht

private def lastStepSignalFreeAt
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      PPL.Modes.Lemma6.signalFreeB C = true)
    (i : Fin n) :
    (C i).signalR.val = 0 := by
  unfold PPL.Modes.Lemma6.signalFreeB
    PPL.Modes.Lemma6.allAgentsB at h
  have hall :=
    lastStepFoldlAndTrueAllTrue
      (List.ofFn
        (fun j : Fin n =>
          decide ((C j).signalR.val = 0)))
      h
  have hm :
      decide ((C i).signalR.val = 0) ∈
        List.ofFn
          (fun j : Fin n =>
            decide ((C j).signalR.val = 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  exact of_decide_eq_true (hall _ hm)

private def lastStepSignalFreeOfAt
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      forall i : Fin n,
        (C i).signalR.val = 0) :
    PPL.Modes.Lemma6.signalFreeB C = true := by
  unfold PPL.Modes.Lemma6.signalFreeB
    PPL.Modes.Lemma6.allAgentsB
  apply lastStepFoldlAndTrueOfAllTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  simp [h i]

private def lastStepAllDetectOfAt
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (h :
      forall i : Fin n,
        (C i).mode = true) :
    PPL.Modes.Lemma6.allDetectB C = true := by
  unfold PPL.Modes.Lemma6.allDetectB
    PPL.Modes.Lemma6.allAgentsB
  apply lastStepFoldlAndTrueOfAllTrue
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, hi⟩ := hb
  rw [← hi]
  simp [h i]

/-! ## Ring geometry for the counterclockwise sweep -/

private def lastStepShiftLeftZero
    {n : Nat}
    (ring : DirectedRing n)
    (base : Fin n) :
    PPL.shiftLeft ring base 0 = base := by
  apply Fin.ext
  simp [PPL.shiftLeft,
    Nat.mod_eq_of_lt base.isLt]

private def lastStepShiftLeftN
    {n : Nat}
    (ring : DirectedRing n)
    (base : Fin n) :
    PPL.shiftLeft ring base n = base := by
  apply Fin.ext
  simp [PPL.shiftLeft,
    Nat.mod_eq_of_lt base.isLt]

/-- One clockwise edge cancels one unit of a bounded left shift. -/
private def lastStepRightShiftLeftPred
    {n : Nat}
    (ring : DirectedRing n)
    (base : Fin n)
    (d : Nat)
    (hd1 : 1 <= d)
    (hdn : d <= n) :
    ring.rightNeighbor
        (PPL.shiftLeft ring base d) =
      PPL.shiftLeft ring base (d - 1) := by
  by_cases heq : d = n
  · subst d
    rw [lastStepShiftLeftN ring base]
    apply Fin.ext
    simp only
      [DirectedRing.rightNeighbor,
        PPL.shiftLeft]
    have hpred :
        n - 1 < n := by
      omega
    rw [Nat.mod_eq_of_lt hpred]
    congr 1
    omega
  · have hdlt : d < n := by
      omega
    have hpred :
        d - 1 < n := by
      omega
    apply Fin.ext
    simp only
      [DirectedRing.rightNeighbor,
        PPL.shiftLeft]
    rw [Nat.mod_eq_of_lt hdlt,
      Nat.mod_eq_of_lt hpred]
    rw [Nat.mod_add_mod]
    congr 1
    omega

/-! ## Smallest remaining literal row -/

/--
Exact selected-pair row needed by the sweep proof.

This is deliberately below the sweep semantics.  It has no base, front,
IsBorder, LastClearedCapped, or schedule argument.

The intended direct proof is a finite unfolding of DetermineMode, Algorithm 2,
both MoveToken rows, and Algorithm 5.  TransitionFacts gives the token frames,
and Elim.otherView gives the Algorithm-5 frame.
-/
def Lemma16LastPairRowSpec : Prop :=
  forall {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa),
    l.leader = false ->
    r.leader = false ->
    l.signalR.val = 0 ->
    r.signalR.val = 0 ->
    l.clock.val = kappa ->
    r.clock.val = kappa ->
    r.dist.val =
      (l.dist.val + 1) % (2 * psi) ->
      let q := PPL.ppl hpsi l r
      And (q.1.clock.val = kappa)
        (And (q.2.clock.val = kappa)
          (And (q.1.mode = true)
            (And (q.2.mode = true)
              (And (q.1.signalR.val = 0)
                (And (q.2.signalR.val = 0)
                  (And (q.1.dist = l.dist)
                    (And (q.2.dist = r.dist)
                      (And
                        (q.1.last =
                          if Or (r.dist.val = 0)
                              (r.dist.val = psi)
                          then false
                          else r.last)
                        (q.2.last = r.last)))))))))

/-! ## Lift the pair row to a full configuration step -/

private def lastStepRightNeighborNeSelf
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private def lastStepPredecessorSafe
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (base : Fin n)
    (C : Config n psi kappa)
    (front d : Nat)
    (hbase : PPL.IsBorder C base)
    (hclear :
      LastClearedCapped
        ring base front C)
    (hd1 : 1 <= d)
    (hdpred : d - 1 <= front)
    (hdn : d <= n) :
    Or
      (PPL.IsBorder C
        (ring.rightNeighbor
          (PPL.shiftLeft ring base d)))
      ((C
        (ring.rightNeighbor
          (PPL.shiftLeft ring base d))).last =
        false) := by
  have hgeom :=
    lastStepRightShiftLeftPred
      ring base d hd1 hdn
  rw [hgeom]
  by_cases hd : d = 1
  · subst d
    rw [lastStepShiftLeftZero]
    exact Or.inl hbase
  · exact
      Or.inr
        (hclear (d - 1)
          (by omega) hdpred)

private def lastStepInitiatorCleared
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (hlast :
      (D e).last =
        if Or
            ((C (ring.rightNeighbor e)).dist.val = 0)
            ((C (ring.rightNeighbor e)).dist.val = psi)
        then false
        else (C (ring.rightNeighbor e)).last)
    (hsafe :
      Or
        (PPL.IsBorder C
          (ring.rightNeighbor e))
        ((C (ring.rightNeighbor e)).last = false)) :
    (D e).last = false := by
  rcases hsafe with hborder | hlast0
  · unfold PPL.IsBorder at hborder
    rcases hborder with hzero | hpsi
    · rw [hlast]
      simp [hzero]
    · rw [hlast]
      simp [hpsi]
  · rw [hlast]
    by_cases hzero :
        (C (ring.rightNeighbor e)).dist.val = 0
    · simp [hzero]
    · by_cases hpsi :
        (C (ring.rightNeighbor e)).dist.val = psi
      · simp [hzero, hpsi]
      · simp [hzero, hpsi, hlast0]

/-! ## Assembly -/

/--
Everything except the exact local pair row is closed here.
-/
theorem lemma16LastForcingCappedStepSpec
    (hrow : Lemma16LastPairRowSpec) :
    Lemma16LastForcingCappedStepSpec := by
  unfold Lemma16LastForcingCappedStepSpec
  intro n psi kappa
  intro hn3 hpsi ring base C front e
  intro hfront hready hbase hclear

  let D : Config n psi kappa :=
    PopulationProtocol.step
      (PPL.protocol psi kappa) ring C e

  change
    Or (PPL.CPB ring D)
      (And
        (DistReadyCapped ring D)
        (And
          (PPL.IsBorder D base)
          (And
            (LastClearedCapped
              ring base front D)
            (e =
                PPL.shiftLeft
                  ring base (front + 1) ->
              front < n ->
              LastClearedCapped
                ring base (front + 1) D))))

  rcases hready with
    ⟨hdetectCapped, hdist⟩
  rcases hdetectCapped with
    ⟨hdetect, hcap⟩
  rcases hdetect with
    ⟨hpeace, hleaderless,
      hsignalFree, _hallDetect⟩

  have hlsignal :
      (C e).signalR.val = 0 :=
    lastStepSignalFreeAt
      C hsignalFree e
  have hrsignal :
      (C (ring.rightNeighbor e)).signalR.val = 0 :=
    lastStepSignalFreeAt
      C hsignalFree
      (ring.rightNeighbor e)

  have hpair :=
    hrow hpsi
      (C e)
      (C (ring.rightNeighbor e))
      (hleaderless e)
      (hleaderless
        (ring.rightNeighbor e))
      hlsignal hrsignal
      (hcap e)
      (hcap (ring.rightNeighbor e))
      (hdist e)

  dsimp only at hpair
  rcases hpair with
    ⟨hclockL, hclockR,
      hmodeL, hmodeR,
      hsignalL, hsignalR,
      hdistL, hdistR,
      hlastL, hlastR⟩

  have hne :
      ring.rightNeighbor e ≠ e :=
    lastStepRightNeighborNeSelf
      hn3 ring e

  have hDleft :
      D e =
        (PPL.ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).1 := by
    simp [D, PopulationProtocol.step,
      PPL.protocol, PPL.transition, hpsi]

  have hDright :
      D (ring.rightNeighbor e) =
        (PPL.ppl hpsi
          (C e)
          (C (ring.rightNeighbor e))).2 := by
    simp [D, PopulationProtocol.step,
      PPL.protocol, PPL.transition,
      hpsi, hne]

  have houtside :
      forall i : Fin n,
        i ≠ e ->
        i ≠ ring.rightNeighbor e ->
        D i = C i := by
    intro i hie hir
    simp [D, PopulationProtocol.step,
      PPL.protocol, hie, hir]
    all_goals rfl

  have hclockD :
      forall i : Fin n,
        (D i).clock.val = kappa := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hclockL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hclockR
      · rw [houtside i hie hir]
        exact hcap i

  have hmodeD :
      forall i : Fin n,
        (D i).mode = true := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hmodeL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hmodeR
      · rw [houtside i hie hir]
        exact
          of_decide_eq_true
            (by
              have hall :=
                lastStepFoldlAndTrueAllTrue
                  (List.ofFn
                    (fun j : Fin n =>
                      decide ((C j).mode = true)))
                  _hallDetect
              have hm :
                  decide ((C i).mode = true) ∈
                    List.ofFn
                      (fun j : Fin n =>
                        decide ((C j).mode = true)) := by
                rw [List.mem_ofFn]
                exact ⟨i, rfl⟩
              exact hall _ hm)

  have hsignalD :
      forall i : Fin n,
        (D i).signalR.val = 0 := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hsignalL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hsignalR
      · rw [houtside i hie hir]
        exact
          lastStepSignalFreeAt
            C hsignalFree i

  have hdistD :
      forall i : Fin n,
        (D i).dist = (C i).dist := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDleft]
      exact hdistL
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        rw [hDright]
        exact hdistR
      · exact
          congrArg
            (fun q : PPL.State psi kappa =>
              q.dist)
            (houtside i hie hir)

  have hlastE :
      (D e).last =
        if Or
            ((C (ring.rightNeighbor e)).dist.val = 0)
            ((C (ring.rightNeighbor e)).dist.val = psi)
        then false
        else
          (C (ring.rightNeighbor e)).last := by
    rw [hDleft]
    exact hlastL

  have hlastAway :
      forall i : Fin n,
        i ≠ e ->
        (D i).last = (C i).last := by
    intro i hie
    by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      rw [hDright]
      exact hlastR
    · exact
        congrArg
          (fun q : PPL.State psi kappa =>
            q.last)
          (houtside i hie hir)

  have hpeaceD :
      AllLivePeaceful ring D := by
    simpa [D] using
      allLivePeaceful_step_closed
        hn3 hpsi ring C e hpeace

  by_cases hleaderD :
      Exists fun i : Fin n =>
        (D i).leader = true
  · exact
      Or.inl
        (cpb_of_allLivePeaceful_hasLeader
          ring D hpeaceD hleaderD)

  · have hleaderlessD :
        forall i : Fin n,
          (D i).leader = false := by
      intro i
      cases hi : (D i).leader with
      | false =>
          rfl
      | true =>
          exact
            False.elim
              (hleaderD ⟨i, hi⟩)

    have hsignalFreeD :
        PPL.Modes.Lemma6.signalFreeB D = true :=
      lastStepSignalFreeOfAt
        D hsignalD

    have hallDetectD :
        PPL.Modes.Lemma6.allDetectB D = true :=
      lastStepAllDetectOfAt
        D hmodeD

    have hdetectD :
        DetectReadyCapped ring D := by
      unfold DetectReadyCapped
      refine
        And.intro ?_ hclockD
      unfold DetectReady
      exact
        And.intro hpeaceD
          (And.intro hleaderlessD
            (And.intro
              hsignalFreeD
              hallDetectD))

    have hdistReadyD :
        forall i : Fin n,
          (D (ring.rightNeighbor i)).dist.val =
            ((D i).dist.val + 1) %
              (2 * psi) := by
      intro i
      rw [hdistD (ring.rightNeighbor i),
        hdistD i]
      exact hdist i

    have hreadyD :
        DistReadyCapped ring D := by
      unfold DistReadyCapped
      exact
        And.intro
          hdetectD hdistReadyD

    have hbaseD :
        PPL.IsBorder D base := by
      unfold PPL.IsBorder at hbase ⊢
      rw [hdistD base]
      exact hbase

    have hclearD :
        LastClearedCapped
          ring base front D := by
      unfold LastClearedCapped
      intro d hd1 hdf
      let x :=
        PPL.shiftLeft ring base d
      by_cases hxe : x = e
      · have hsafe0 :=
          lastStepPredecessorSafe
            ring base C front d
            hbase hclear hd1
            (by omega)
            (Nat.le_trans hdf hfront)
        have hsafe :
            Or
              (PPL.IsBorder C
                (ring.rightNeighbor e))
              ((C (ring.rightNeighbor e)).last =
                false) := by
          change
            Or
              (PPL.IsBorder C
                (ring.rightNeighbor x))
              ((C (ring.rightNeighbor x)).last =
                false)
            at hsafe0
          rw [hxe] at hsafe0
          exact hsafe0
        have heFalse :=
          lastStepInitiatorCleared
            ring C D e hlastE hsafe
        change (D x).last = false
        rw [hxe]
        exact heFalse
      · change (D x).last = false
        calc
          (D x).last =
              (C x).last :=
            hlastAway x hxe
          _ = false :=
            hclear d hd1 hdf

    refine
      Or.inr
        (And.intro hreadyD
          (And.intro hbaseD
            (And.intro hclearD ?_)))

    intro he hfrontLt
    unfold LastClearedCapped
    intro d hd1 hdnext
    by_cases hdf : d <= front
    · exact hclearD d hd1 hdf
    · have hdeq :
          d = front + 1 := by
        omega
      have hdn :
          d <= n := by
        omega
      have hsafe0 :=
        lastStepPredecessorSafe
          ring base C front d
          hbase hclear hd1
          (by omega) hdn
      have hx :
          PPL.shiftLeft ring base d = e := by
        rw [hdeq]
        exact he.symm
      have hsafe :
          Or
            (PPL.IsBorder C
              (ring.rightNeighbor e))
            ((C (ring.rightNeighbor e)).last =
              false) := by
        change
          Or
            (PPL.IsBorder C
              (ring.rightNeighbor
                (PPL.shiftLeft ring base d)))
            ((C
              (ring.rightNeighbor
                (PPL.shiftLeft ring base d))).last =
              false)
          at hsafe0
        rw [hx] at hsafe0
        exact hsafe0
      have heFalse :=
        lastStepInitiatorCleared
          ring C D e hlastE hsafe
      rw [hx]
      exact heFalse

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16LastForcingCappedStepSpec
