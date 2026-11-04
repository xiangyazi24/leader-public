import Leader.Wu.Splice.NoRouteGenerationStages
import Leader.Wu.Splice.NoRouteDoneStages
import Leader.Wu.Birth.GenerationDonePhase
import Leader.Wu.Protocol.Repairs


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CleanupEndpointDepartSeed


open PPLL PPLLRepair PPLLResearchFormulation PPLLComparisonHistory
open BirthGenerationControlRepair BirthGenerationDone
open B9NoRouteStagesB


variable {psi : Nat}


def Seed (u : AgentState psi) : Prop :=
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none


def MoveSeed (l r : AgentState psi) : Prop :=
  LeftZeroDepart l ∧ l.path2 = none ∧ r.path2 = none


def GenSeed (l r : AgentState psi) : Prop :=
  MoveSeed l r ∧ NoEqualOnPair l r ∧ r.state ≠ .eliminate_signal


theorem seed_of_view (u v : AgentState psi)
    (h : ComparisonTrackedView.ofState u = ComparisonTrackedView.ofState v)
    (hv : Seed v) : Seed u := by
  rcases hv with ⟨hs, hp, h2⟩
  exact ⟨(congrArg ComparisonTrackedView.state h).trans hs,
    (congrArg ComparisonTrackedView.path h).trans hp,
    (congrArg ComparisonTrackedView.path2 h).trans h2⟩


private theorem finish_left_path (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (genSigSaturatedFinish hpsi l r).1.path = l.path := by
  unfold genSigSaturatedFinish
  dsimp only
  split <;> rfl


private theorem gen_leftZero (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : AgentState psi) (hl : Seed l) :
    LeftZeroDepart (genCleanAfterWait hpsi l r).1 := by
  let s := genSigSaturatedStart hpsi l r
  let e := genCleanEmit hpsi s.1 s.2
  let g := genCleanPropagate hpsi e.1 e.2
  have hs : s.1.path = .bot := by
    have h : s.1.path = l.path := by
      unfold s genSigSaturatedStart
      dsimp only
      split <;> rfl
    exact h.trans hl.2.1
  have he : e.1.path = .bot := by
    have h : e.1.path = s.1.path := by
      unfold e genCleanEmit
      rfl
    exact h.trans hs
  intro b hout
  change (genSigSaturatedFinish hpsi g.1 g.2).1.path = .some 0 b at hout
  have hpath : g.1.path = .some 0 b :=
    (finish_left_path hpsi g.1 g.2).symm.trans hout
  by_cases hp : e.1.label ≠ ⟨psi - 1, by omega⟩ ∧
      e.1.state = .produce ∧ e.2.state = .done
  · have hw := genCleanPropagate_writer hpsi e.1 e.2
      hp.1 hp.2.1 hp.2.2
    have hwritePath :
        (genCleanPropagate hpsi e.1 e.2).1.path =
          .some e.1.label.val (if e.1.bit then 1 else 0) := by
      exact congrArg
        (fun q : AgentState psi × AgentState psi => q.1.path) hw
    have hwritePathG :
        g.1.path = .some e.1.label.val (if e.1.bit then 1 else 0) := by
      simpa only [g] using hwritePath
    have hsame :
        PathInfo.some e.1.label.val (if e.1.bit then 1 else 0) = .some 0 b :=
      hwritePathG.symm.trans hpath
    have hv := congrArg
      (fun x : PathInfo => match x with | .bot => 0 | .some a _ => a) hsame
    change e.1.label.val = 0 at hv
    have hz : e.1.label = ⟨0, hpsi⟩ := Fin.ext hv
    have hf := gen_zero_ack_finish hpsi (by omega) e.1 e.2
      hz hp.2.1 hp.2.2
    have hstate := congrArg
      (fun q : AgentState psi × AgentState psi => q.1.state) hf
    change (genSigSaturatedFinish hpsi g.1 g.2).1.state = .depart
    simpa only [g] using hstate
  · have hg : g = (e.1, e.2) := by
      unfold g genCleanPropagate
      rw [if_neg hp]
    rw [hg] at hpath
    rw [he] at hpath
    cases hpath


private theorem gen_right_not_eliminate (hpsi : 0 < psi)
    (l r : AgentState psi) (hr : Seed r) :
    (genCleanAfterWait hpsi l r).2.state ≠ .eliminate_signal := by
  let s := genSigSaturatedStart hpsi l r
  have hs : s.2.state ≠ .eliminate_signal := by
    unfold s genSigSaturatedStart
    dsimp only
    split
    · split
      · change MainState.produce ≠ MainState.eliminate_signal
        intro h; cases h
      · rw [hr.1]
        intro h; cases h
    · split
      · change MainState.produce ≠ MainState.eliminate_signal
        intro h; cases h
      · rw [hr.1]
        intro h; cases h
  let e := genCleanEmit hpsi s.1 s.2
  have he : e.2.state ≠ .eliminate_signal := by
    unfold e genCleanEmit
    dsimp only
    split
    · change MainState.done ≠ MainState.eliminate_signal
      intro h; cases h
    · exact hs
  let g := genCleanPropagate hpsi e.1 e.2
  have hg : g.2.state ≠ .eliminate_signal := by
    unfold g genCleanPropagate
    split
    · change MainState.depart ≠ MainState.eliminate_signal
      intro h; cases h
    · exact he
  change (genSigSaturatedFinish hpsi g.1 g.2).2.state ≠ .eliminate_signal
  exact hg


theorem gen_seed (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : AgentState psi) (hl : Seed l) (hr : Seed r) :
    let q := genCleanAfterWait hpsi l r
    GenSeed q.1 q.2 := by
  have h0 : B9NoRouteStagesA.NoEqualOnPair (l, r) := by
    refine ⟨⟨?_, hl.2.2⟩, ⟨?_, hr.2.2⟩⟩
    · rw [hl.1]; decide
    · rw [hr.1]; decide
  have hn := B9NoRouteStagesA.gensig_noEqualOnPair hpsi l r h0
  change B9NoRouteStagesA.NoEqualOnPair (genCleanAfterWait hpsi l r) at hn
  have hz := gen_leftZero hpsi h2 l r hl
  have hre := gen_right_not_eliminate hpsi l r hr
  exact ⟨⟨hz, hn.1.2, hn.2.2⟩, ⟨hn.1.1, hn.2.1⟩, hre⟩


theorem clean_seed (hpsi : 0 < psi) (l r : AgentState psi)
    (h : GenSeed l r) :
    let q := cleanSig hpsi l r
    GenSeed q.1 q.2 := by
  rcases h with ⟨⟨hz, hl2, hr2⟩, hne, hre⟩
  have hf := cleanSig_comparison_frame hpsi l r
  rcases hf with ⟨hpl, _, hsl, hsr, h2l, h2r⟩
  refine ⟨⟨?_, h2l.trans hl2, h2r.trans hr2⟩, ⟨?_, ?_⟩, ?_⟩
  · intro b hp
    rcases hpl with hb | hk
    · have hbad : (PathInfo.bot : PathInfo) = .some 0 b := hb.symm.trans hp
      cases hbad
    · exact hsl.trans (hz b (hk.symm.trans hp))
  · intro he; exact hne.1 (hsl.symm.trans he)
  · intro he; exact hne.2 (hsr.symm.trans he)
  · intro he; exact hre (hsr.symm.trans he)


end B9CleanupEndpointDepartSeed


#print axioms B9CleanupEndpointDepartSeed.gen_seed
#print axioms B9CleanupEndpointDepartSeed.clean_seed
