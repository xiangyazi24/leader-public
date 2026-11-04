import Leader.Wu.Splice.CheckWholeStepHistory


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckWholeStep


open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair
open PPLLComparisonHistory
open BirthGenerationDone BirthStationaryWrite


private def rawOfAuthorized {n psi : Nat}
    (q : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    MarkedAgentState n psi × MarkedAgentState n psi :=
  (⟨q.1.concrete.core, q.1.history⟩,
    ⟨q.2.concrete.core, q.2.history⟩)


private def authorizedWithHistory {n psi : Nat}
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (m : MarkedAgentState n psi × MarkedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  (⟨q.1, m.1.history⟩, ⟨q.2, m.2.history⟩)


private theorem rawOfAuthorized_trusted {n psi : Nat}
    (q : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi)
    (h : AuthorizedPairHistoryTrusted q) :
    RawPairHistoryTrusted (rawOfAuthorized q) := by
  simpa [rawOfAuthorized, AuthorizedPairHistoryTrusted,
    RawPairHistoryTrusted] using h


private theorem authorizedWithHistory_trusted {n psi : Nat}
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (m : MarkedAgentState n psi × MarkedAgentState n psi)
    (hcore : (q.1.core, q.2.core) =
      (m.1.concrete, m.2.concrete))
    (hm : RawPairHistoryTrusted m) :
    AuthorizedPairHistoryTrusted (authorizedWithHistory q m) := by
  obtain ⟨hL, hR⟩ := Prod.mk.inj hcore
  change FullLocalHistoryTrusted q.1.core m.1.history ∧
    FullLocalHistoryTrusted q.2.core m.2.history
  change FullLocalHistoryTrusted m.1.concrete m.1.history ∧
    FullLocalHistoryTrusted m.2.concrete m.2.history at hm
  rw [hL, hR]
  exact hm


/-! P-prime wall -> GEN cut. -/


private def markedAuthorizedPPrime {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let raw := rawOfAuthorized (l, r)
  let m := Q11525CurrentHistoryFrames.markedPPsiLeaderResetProbeWall
    hpsi raw.1 raw.2
  let q := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hpsi l.concrete r.concrete
  authorizedWithHistory q m


private theorem markedAuthorizedPPrime_preserves
    {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi)
    (hin : AuthorizedPairHistoryTrusted (l, r)) :
    AuthorizedPairHistoryTrusted (markedAuthorizedPPrime hpsi l r) := by
  let raw := rawOfAuthorized (l, r)
  let m := Q11525CurrentHistoryFrames.markedPPsiLeaderResetProbeWall
    hpsi raw.1 raw.2
  let q := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hpsi l.concrete r.concrete
  have hi := rawOfAuthorized_trusted (l, r) hin
  have hm :=
    Q11525CurrentHistoryFrames.markedPPsiLeaderResetProbeWall_preserves_fullLocalHistoryTrusted
      hpsi raw.1 raw.2 hi.1 hi.2
  change RawPairHistoryTrusted m at hm
  have hc := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core
    hpsi l.concrete r.concrete
  change (q.1.core, q.2.core) =
    PPLLWallSweepRepair.pPsiLeaderResetProbeWall
      hpsi l.concrete.core r.concrete.core at hc
  have he := Q11525CurrentHistoryFrames.erase_markedPPsiLeaderResetProbeWall
    hpsi raw.1 raw.2
  change (m.1.concrete, m.2.concrete) =
    PPLLWallSweepRepair.pPsiLeaderResetProbeWall
      hpsi raw.1.concrete raw.2.concrete at he
  have he' : (m.1.concrete, m.2.concrete) =
      PPLLWallSweepRepair.pPsiLeaderResetProbeWall
        hpsi l.concrete.core r.concrete.core := by
    simpa [raw, rawOfAuthorized] using he
  change AuthorizedPairHistoryTrusted (authorizedWithHistory q m)
  exact authorizedWithHistory_trusted q m (hc.trans he'.symm) hm


/-! GEN -> DONE cut: the exact current CLEAN/ELIMINATE marked tail. -/


def markedCurrentCleanEliminate {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let raw := rawOfAuthorized (l, r)
  let c := markedCleanSig hpsi raw.1 raw.2
  let e := markedEliminateSig hpsi c.1 c.2
  let pc := authorizedCleanSig hpsi l.concrete r.concrete
  let pe := authorizedEliminateSig hpsi pc.1 pc.2
  authorizedWithHistory pe e


/-- Exact missing strength on current main. `markedCleanSig` and
`markedEliminateSig` exist and erase exactly, but export only Audit trust;
the absent conjunct is the framed `pCarry` history. -/
def CurrentCleanEliminateFullPreservation {n psi : Nat}
    (hpsi : 0 < psi) : Prop :=
  ∀ (l r : MarkedAuthorizedAgentState n psi),
    AuthorizedPairHistoryTrusted (l, r) →
    AuthorizedPairHistoryTrusted (markedCurrentCleanEliminate hpsi l r)


/-! DONE -> CHECK cut: physical DONE adapter, reset wall, sanitizer. -/


private def markedDoneResetSanitize {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let raw := rawOfAuthorized (l, r)
  let m := markedDoneCaptureSigMove hpsi raw.1 raw.2
  let q := BirthGenerationDone.authorizedDoneMove hpsi l.concrete r.concrete
  let a := authorizedWithHistory q m
  let w := markedPreCheckResetWall a.1 a.2
  markedSanitizeAuthorizedPair hpsi w.1 w.2


private theorem markedDoneResetSanitize_of_done_trusted
    {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi)
    (hm : RawPairHistoryTrusted
      (markedDoneCaptureSigMove hpsi
        (rawOfAuthorized (l, r)).1 (rawOfAuthorized (l, r)).2)) :
    AuthorizedPairHistoryTrusted (markedDoneResetSanitize hpsi l r) := by
  let raw := rawOfAuthorized (l, r)
  let m := markedDoneCaptureSigMove hpsi raw.1 raw.2
  let q := BirthGenerationDone.authorizedDoneMove hpsi l.concrete r.concrete
  let a := authorizedWithHistory q m
  have hm' : RawPairHistoryTrusted m := by
    simpa [m, raw] using hm
  have hc := BirthGenerationDone.authorizedDoneMove_core
    hpsi l.concrete r.concrete
  change (q.1.core, q.2.core) =
    BirthGenerationDone.doneCaptureSigMove
      hpsi l.concrete.core r.concrete.core at hc
  have he := erase_markedDoneCaptureSigMove hpsi raw.1 raw.2
  change (m.1.concrete, m.2.concrete) =
    BirthGenerationDone.doneCaptureSigMove
      hpsi raw.1.concrete raw.2.concrete at he
  have he' : (m.1.concrete, m.2.concrete) =
      BirthGenerationDone.doneCaptureSigMove
        hpsi l.concrete.core r.concrete.core := by
    simpa [raw, rawOfAuthorized] using he
  have ha := authorizedWithHistory_trusted q m (hc.trans he'.symm) hm'
  let w := markedPreCheckResetWall a.1 a.2
  have hw := markedPreCheckResetWall_preserves_fullLocalHistoryTrusted
    a.1 a.2 ha.1 ha.2
  change AuthorizedPairHistoryTrusted w at hw
  have hs := markedSanitizeAuthorizedPair_preserves_fullLocalHistoryTrusted
    hpsi w.1 w.2 hw.1 hw.2
  change AuthorizedPairHistoryTrusted
    (markedSanitizeAuthorizedPair hpsi w.1 w.2) at hs
  simpa only [markedDoneResetSanitize, raw, m, q, a, w] using hs


/-! DISAPPEAR raw marked output -> authorized COMPARE cut. -/


private def markedAuthorizedDisappear {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let raw := rawOfAuthorized (l, r)
  let m := markedDisappear hpsi raw.1 raw.2
  let q := authorizedDisappear hpsi l.concrete r.concrete
  authorizedWithHistory q m


private theorem markedAuthorizedDisappear_of_disappear_trusted
    {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi)
    (hm : RawPairHistoryTrusted
      (markedDisappear hpsi
        (rawOfAuthorized (l, r)).1 (rawOfAuthorized (l, r)).2)) :
    AuthorizedPairHistoryTrusted (markedAuthorizedDisappear hpsi l r) := by
  let raw := rawOfAuthorized (l, r)
  let m := markedDisappear hpsi raw.1 raw.2
  let q := authorizedDisappear hpsi l.concrete r.concrete
  have hm' : RawPairHistoryTrusted m := by
    simpa [m, raw] using hm
  have hc : (q.1.core, q.2.core) =
      disappear hpsi l.concrete.core r.concrete.core := by
    rfl
  have he := erase_markedDisappear hpsi raw.1 raw.2
  change (m.1.concrete, m.2.concrete) =
    disappear hpsi raw.1.concrete raw.2.concrete at he
  have he' : (m.1.concrete, m.2.concrete) =
      disappear hpsi l.concrete.core r.concrete.core := by
    simpa [raw, rawOfAuthorized] using he
  change AuthorizedPairHistoryTrusted (authorizedWithHistory q m)
  exact authorizedWithHistory_trusted q m (hc.trans he'.symm) hm'


/-! Stationary persistent WRITE authorized adapter. -/


private def markedAuthorizedStationary {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let raw := rawOfAuthorized (l, r)
  let m := Q11515ImmediateHistoryLift.markedStationaryPersistentRaw
    hpsi raw.1 raw.2
  let q := BirthStationaryWrite.stationaryPersistentAuthorizedRow
    hpsi l.concrete r.concrete
  authorizedWithHistory q m


private theorem markedAuthorizedStationary_preserves
    {n psi : Nat} (hpsi : 0 < psi)
    (l r : MarkedAuthorizedAgentState n psi)
    (hin : AuthorizedPairHistoryTrusted (l, r)) :
    AuthorizedPairHistoryTrusted (markedAuthorizedStationary hpsi l r) := by
  let raw := rawOfAuthorized (l, r)
  let m := Q11515ImmediateHistoryLift.markedStationaryPersistentRaw
    hpsi raw.1 raw.2
  let q := BirthStationaryWrite.stationaryPersistentAuthorizedRow
    hpsi l.concrete r.concrete
  have hi := rawOfAuthorized_trusted (l, r) hin
  have hm :=
    Q11515ImmediateHistoryLift.markedStationaryPersistentRaw_preserves_fullLocalHistoryTrusted
      hpsi raw.1 raw.2 hi.1 hi.2
  change RawPairHistoryTrusted m at hm
  have hc := BirthStationaryWrite.stationaryPersistentAuthorizedRow_core
    hpsi l.concrete r.concrete
  change (q.1.core, q.2.core) =
    BirthStationaryWrite.stationaryPersistentRaw
      hpsi l.concrete.core r.concrete.core at hc
  have he := Q11515ImmediateHistoryLift.erase_markedStationaryPersistentRaw
    hpsi raw.1 raw.2
  change (m.1.concrete, m.2.concrete) =
    BirthStationaryWrite.stationaryPersistentRaw
      hpsi raw.1.concrete raw.2.concrete at he
  have he' : (m.1.concrete, m.2.concrete) =
      BirthStationaryWrite.stationaryPersistentRaw
        hpsi l.concrete.core r.concrete.core := by
    simpa [raw, rawOfAuthorized] using he
  change AuthorizedPairHistoryTrusted (authorizedWithHistory q m)
  exact authorizedWithHistory_trusted q m (hc.trans he'.symm) hm


/-! Literal five source-join cuts. -/


private def genInputOf {n psi : Nat} (hpsi : 0 < psi)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  markedAuthorizedPPrime hpsi input.1 input.2


private def genOutputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  let g := genInputOf hpsi input
  markedAuthorizedGenCleanEntryWidth
    hpsi hwidth hle kappa sourcePos g.1 g.2


private def doneAuthorizedOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  let g := genOutputOf hpsi hwidth hle kappa sourcePos input
  markedCurrentCleanEliminate hpsi g.1 g.2


private def doneInputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  rawOfAuthorized (doneAuthorizedOf
    hpsi hwidth hle kappa sourcePos input)


private def checkInputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  let d := doneAuthorizedOf hpsi hwidth hle kappa sourcePos input
  markedDoneResetSanitize hpsi d.1 d.2


private def checkOutputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  let c := checkInputOf hpsi hwidth hle kappa sourcePos input
  markedPreserveDoneCheck hpsi c.1 c.2


private def disappearInputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  rawOfAuthorized (checkOutputOf hpsi hwidth hle kappa sourcePos input)


private def compareInputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :=
  let c := checkOutputOf hpsi hwidth hle kappa sourcePos input
  markedAuthorizedDisappear hpsi c.1 c.2


/-- CHECK output -> raw DISAPPEAR input, without exposing the CHECK row. -/
private theorem check_to_disappear_join
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    AuthorizedPairHistoryTrusted
        (checkOutputOf hpsi hwidth hle kappa sourcePos input) →
      RawPairHistoryTrusted
        (disappearInputOf hpsi hwidth hle kappa sourcePos input) := by
  intro hc
  unfold disappearInputOf
  exact rawOfAuthorized_trusted _ hc


/-- DISAPPEAR output -> COMPARE cut.  Only the two one-line cut wrappers are
unfolded; the CHECK output is immediately generalized to an opaque pair. -/
private theorem disappear_to_compare_join
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    let q := markedDisappear hpsi
      (disappearInputOf hpsi hwidth hle kappa sourcePos input).1
      (disappearInputOf hpsi hwidth hle kappa sourcePos input).2
    RawPairHistoryTrusted q →
      AuthorizedPairHistoryTrusted
        (compareInputOf hpsi hwidth hle kappa sourcePos input) := by
  unfold disappearInputOf compareInputOf
  generalize hC :
    checkOutputOf hpsi hwidth hle kappa sourcePos input = c
  rcases c with ⟨l, r⟩
  exact markedAuthorizedDisappear_of_disappear_trusted hpsi l r


/-- The five actual source-join cuts of the literal current ordinary row. -/
def cutsOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) : StepHistoryCuts n psi :=
  { sourcePos := sourcePos
    genInput := genInputOf hpsi input
    doneInput := doneInputOf hpsi hwidth hle kappa sourcePos input
    checkInput := checkInputOf hpsi hwidth hle kappa sourcePos input
    disappearInput := disappearInputOf hpsi hwidth hle kappa sourcePos input
    compareInput := compareInputOf hpsi hwidth hle kappa sourcePos input }


/-- Opaque post-COMPARE tail.  Its inputs are already small pair variables, so
none of its local lets can force normalization of the preceding whole row. -/
private def literalTailOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (input a : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  let c := markedAuthorizedCompareSigActionOne hpsi a.1 a.2
  let s := markedAuthorizedSuppressWidth hpsi hwidth hle c.1 c.2
  let w := markedAuthorizedStationary hpsi s.1 s.2
  let born := K2BirthDispatcher.authBirth
    input.1.concrete input.2.concrete (w.1.concrete, w.2.concrete)
  markedMarkLeaderBirth born w.1 w.2


/-- Literal tail after the COMPARE cut: COMPARE, short SUPPRESS, stationary
persistent WRITE, then the observed birth mark. -/
def literalOutputOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi :=
  literalTailOf hpsi hwidth hle input
    (compareInputOf hpsi hwidth hle kappa sourcePos input)


/-- Full trust through the post-COMPARE tail.  Each stage output is generalized
before the next lift, so no preceding row term is ever unfolded by `change`. -/
private theorem literalTailOf_preserves
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (input a : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi)
    (hc : AuthorizedPairHistoryTrusted
      (markedAuthorizedCompareSigActionOne hpsi a.1 a.2)) :
    AuthorizedPairHistoryTrusted
      (literalTailOf hpsi hwidth hle input a) := by
  unfold literalTailOf
  generalize hC :
    markedAuthorizedCompareSigActionOne hpsi a.1 a.2 = c at hc ⊢


  have hs0 :=
    markedAuthorizedSuppressWidth_preserves_fullLocalHistoryTrusted
      hpsi hwidth hle c.1 c.2 hc.1 hc.2
  generalize hS :
    markedAuthorizedSuppressWidth hpsi hwidth hle c.1 c.2 = s at hs0
  have hs : AuthorizedPairHistoryTrusted s := by
    exact hs0


  have hw0 := markedAuthorizedStationary_preserves
    hpsi s.1 s.2 hs
  generalize hW : markedAuthorizedStationary hpsi s.1 s.2 = w at hw0
  have hw : AuthorizedPairHistoryTrusted w := by
    exact hw0


  let born := K2BirthDispatcher.authBirth
    input.1.concrete input.2.concrete (w.1.concrete, w.2.concrete)
  have hb0 := markedMarkLeaderBirth_preserves_fullLocalHistoryTrusted
    born w.1 w.2 hw.1 hw.2
  have hb : AuthorizedPairHistoryTrusted
      (markedMarkLeaderBirth born w.1 w.2) := by
    exact hb0
  simpa only [hS, hW, born] using hb


/-- COMPARE cut -> literal output.  `compareInputOf` is generalized before the
post-COMPARE preservation lemma is instantiated; `literalOutputOf` is unfolded
only once, after the heavy cut has become the opaque variable `a`. -/
private theorem compare_to_output_join
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) :
    let q := markedAuthorizedCompareSigActionOne hpsi
      (compareInputOf hpsi hwidth hle kappa sourcePos input).1
      (compareInputOf hpsi hwidth hle kappa sourcePos input).2
    AuthorizedPairHistoryTrusted q →
      AuthorizedPairHistoryTrusted
        (literalOutputOf hpsi hwidth hle kappa sourcePos input) := by
  generalize hA :
    compareInputOf hpsi hwidth hle kappa sourcePos input = a
  intro _q hc
  have ht := literalTailOf_preserves hpsi hwidth hle input a hc
  simpa only [literalOutputOf, hA] using ht


/-- Complete proof-only trace for the literal current ordinary row. -/
def traceOf {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi)
    (hCE : CurrentCleanEliminateFullPreservation (n := n) hpsi) :
    WholeStepHistoryTrace (n := n) hpsi hwidth hle kappa where
  input := input
  output := literalOutputOf hpsi hwidth hle kappa sourcePos input
  cuts := cutsOf hpsi hwidth hle kappa sourcePos input
  input_to_gen := by
    intro hin
    exact markedAuthorizedPPrime_preserves hpsi input.1 input.2 hin
  gen_to_done := by
    change AuthorizedPairHistoryTrusted
        (genOutputOf hpsi hwidth hle kappa sourcePos input) →
      RawPairHistoryTrusted
        (doneInputOf hpsi hwidth hle kappa sourcePos input)
    intro hg
    have hce := hCE
      (genOutputOf hpsi hwidth hle kappa sourcePos input).1
      (genOutputOf hpsi hwidth hle kappa sourcePos input).2 hg
    exact rawOfAuthorized_trusted _ hce
  done_to_check := by
    let d := doneAuthorizedOf hpsi hwidth hle kappa sourcePos input
    change RawPairHistoryTrusted
        (markedDoneCaptureSigMove hpsi
          (rawOfAuthorized d).1 (rawOfAuthorized d).2) →
      AuthorizedPairHistoryTrusted (markedDoneResetSanitize hpsi d.1 d.2)
    intro hd
    exact markedDoneResetSanitize_of_done_trusted hpsi d.1 d.2 hd
  check_to_disappear := by
    simpa only [cutsOf, checkOutputOf] using
      (check_to_disappear_join
        hpsi hwidth hle kappa sourcePos input)
  disappear_to_compare := by
    simpa only [cutsOf] using
      (disappear_to_compare_join
        hpsi hwidth hle kappa sourcePos input)
  compare_to_output := by
    simpa only [cutsOf] using
      (compare_to_output_join
        hpsi hwidth hle kappa sourcePos input)


/-- The composition theorem specialized to the actual cuts. -/
theorem markedWholeStep_preserves_fullLocalHistoryTrusted_literal
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (sourcePos : Fin n)
    (input : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi)
    (hCE : CurrentCleanEliminateFullPreservation (n := n) hpsi)
    (hcompat : StepHistoryCompatible hpsi hwidth hle kappa
      (cutsOf hpsi hwidth hle kappa sourcePos input))
    (hin : AuthorizedPairHistoryTrusted input) :
    AuthorizedPairHistoryTrusted
      (literalOutputOf hpsi hwidth hle kappa sourcePos input) := by
  exact markedWholeStep_preserves_fullLocalHistoryTrusted
    hpsi hwidth hle kappa
    (traceOf hpsi hwidth hle kappa sourcePos input hCE)
    hcompat hin


end B9CheckWholeStep


#print axioms B9CheckWholeStep.markedWholeStep_preserves_fullLocalHistoryTrusted_literal
