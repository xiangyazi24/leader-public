import Leader.PPL.ReachCPB.MismatchHistFreshBranchRowGeom
import Init.Omega
namespace PPL.Convergence.ReachCPB
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
/-! -------------------------------------------------------------------------
        1. Geometry check
------------------------------------------------------------------------- -/
private theorem q19945Hpsi : 2 <= 2 := by
        omega
private def q19945Ring : DirectedRing 4 :=
        ⟨by decide⟩
private def q19945E0 : Fin 4 := ⟨0, by decide⟩
private def q19945E1 : Fin 4 := ⟨1, by decide⟩
private def q19945E2 : Fin 4 := ⟨2, by decide⟩
private def q19945E3 : Fin 4 := ⟨3, by decide⟩
/--
The witness used k=0, b=3, psi=2.
The geometry premise forces b=2, so that witness is excluded.
-/
theorem q19945_q19912_geometry_excluded :
        Not
                (Lemma16PostEpochFreshBorderGeometry
                        q19945Ring q19945E3 q19945E0 2) := by
        unfold Lemma16PostEpochFreshBorderGeometry
        decide
/-! -------------------------------------------------------------------------
        1. A new finite witness: geometry holds, but birth metadata is incoherent
------------------------------------------------------------------------- -/
private def q19945Token : PPL.TokenData 2 :=
        ((PPL.offsetOneCode 2 q19945Hpsi, (0 : Fin 2)), (0 : Fin 2))
private def q19945State (i : Fin 4) : PPL.State 2 1 :=
        {
                leader := false
                id :=
                        if Or (i = q19945E1) (i = q19945E2) then
                                true
                        else
                                false
                dist := ⟨i.val, by omega⟩
                last := false
                tokenB :=
                        if i = q19945E2 then
                                some q19945Token
                        else
                                none
                tokenW := none
                mode := true
                clock := (1 : Fin 2)
                signalR := 0
                hits := 0
                bullet := 0
                shield := false
                signalB := false
        }
private def q19945C : Config 4 2 1 :=
        q19945State
/--
The deliberate noncanonical field is birthStep=1 while the LineageId says
born at step 0.  The current local row does not forbid this.
-/
private def q19945Z : PPL.GhostToken 4 2 :=
        {
                value := q19945Token
                lmeta :=
                        {
                                id := .born .black 0
                                birthSite := q19945E0
                                birthStep := 1
                                moves := 4
                        }
        }
private def q19945G : PPL.GhostConfig 4 2 1 :=
        {
                phys := q19945C
                black := fun i =>
                        if i = q19945E2 then some q19945Z else none
                white := fun _ => none
                completed := []
        }
private def q19945M : PPL.LineageMeta 4 :=
        {
                id := .born .black 0
                birthSite := q19945E0
                birthStep := 1
                moves := 5
        }
private theorem q19945_owner_shape
        {i : Fin 4} {z : PPL.GhostToken 4 2}
        (h :
                PPL.ghostTokenAt .black q19945G i = some z) :
        And (i = q19945E2) (z = q19945Z) := by
        by_cases hi : i = q19945E2
        · subst i
          have hz : q19945Z = z := by
                simpa [q19945G, PPL.ghostTokenAt] using h
          exact And.intro rfl hz.symm
        · have hf : False := by
                simpa [q19945G, PPL.ghostTokenAt, hi] using h
          exact False.elim hf
private theorem q19945_geometry :
        Lemma16PostEpochFreshBorderGeometry
                q19945Ring q19945E2 q19945E0 2 := by
        unfold Lemma16PostEpochFreshBorderGeometry
        decide
private theorem q19945_ready :
        DetectReadyCapped q19945Ring q19945G.phys := by
        unfold DetectReadyCapped DetectReady
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · exact
                @of_decide_eq_true _
                        (instDecidableAllLivePeaceful _ _) rfl
        all_goals decide
private theorem q19945_bad :
        Lemma16BadBorderWitness
                q19945Ring q19945G.phys
                q19945E2 q19945E0 .black := by
        unfold Lemma16BadBorderWitness PPL.IsBorder PPL.Cd
        dsimp only
        decide
/--
The state invariant does not see q19945Z: it is gated by epoch <= t,
where the encoded t is 0 and epoch is 1.
-/
private theorem q19945_stateInvariant :
        Lemma16PostEpochFreshStateInvariant
                q19945Ring q19945C 1
                q19945E2 q19945E0 .black q19945G := by
        unfold Lemma16PostEpochFreshStateInvariant
        refine And.intro (fun i => by rfl) ?_
        unfold Lemma16PostEpochFreshLiveInvariant
        intro i z t howner hid _hsite hepoch _hprior
        rcases q19945_owner_shape howner with ⟨hi, hz⟩
        subst i
        subst z
        have ht : t = 0 := by
                change
                        PPL.LineageId.born .black 0 =
                                PPL.LineageId.born .black t
                        at hid
                cases hid
                rfl
        subst t
        omega
/--
The terminal-row history premise does see q19945Z, but it asks only for a
lower bound on birthStep.  Here 1 <= birthStep is true.
-/
private theorem q19945_history :
        forall (i : Fin 4) (z : PPL.GhostToken 4 2) (t : Nat),
                PPL.ghostTokenAt .black q19945G i = some z ->
                z.lmeta.id = .born .black t ->
                z.lmeta.birthSite = q19945E0 ->
                1 <= z.lmeta.birthStep := by
        intro i z t howner _hid _hsite
        rcases q19945_owner_shape howner with ⟨hi, hz⟩
        subst i
        subst z
        change 1 <= 1
        omega
private theorem q19945_fresh :
        PPL.FreshCompletion
                (psi := 2) .black q19945E0 q19945M := by
        unfold PPL.FreshCompletion PPL.FreshAt
        refine And.intro ?_ ?_
        · exact ⟨0, rfl, rfl⟩
        · decide
private theorem q19945_not_old :
        q19945M ∉ q19945G.completed := by
        simp [q19945G]
/--
The direct selected black c=1 move compares false with responder id=false.
It logs moves=5.  The simultaneous white stage can create/move a white token,
but it does not add a terminal completion.
-/
private theorem q19945_post_completed :
        (PPL.ghostStep
                q19945Hpsi q19945Ring 2 q19945G q19945E2).completed =
                        [q19945M] := by
        decide
private theorem q19945_new_member :
        q19945M ∈
                (PPL.ghostStep
                        q19945Hpsi q19945Ring 2 q19945G q19945E2).completed := by
        rw [q19945_post_completed]
        simp
private theorem q19945_post_leaderless :
        forall i : Fin 4,
                ((PPL.ghostStep
                        q19945Hpsi q19945Ring 2 q19945G q19945E2).phys i).leader =
                                false := by
        decide
private theorem q19945_post_not_cpb :
        Not
                (PPL.CPB q19945Ring
                        (PPL.ghostStep
                                q19945Hpsi q19945Ring 2 q19945G q19945E2).phys) := by
        intro hcpb
        unfold PPL.CPB PPL.CPBCore at hcpb
        rcases hcpb.1 with ⟨i, hi⟩
        dsimp only at hi
        rw [q19945_post_leaderless i] at hi
        contradiction
/--
FALSE: geometry alone does not make the arbitrary-G terminal row sound.
-/
theorem lemma16PostEpochFreshNewCompletionStepGeom_refuted :
        Not Lemma16PostEpochFreshNewCompletionStepGeom := by
        intro hrow
        unfold Lemma16PostEpochFreshNewCompletionStepGeom at hrow
        have hs :=
                hrow
                        (n := 4) (psi := 2) (kappa := 1)
                        q19945Hpsi
                        (by decide : 3 <= 4)
                        q19945Ring
                        q19945C
                        1
                        q19945E2
                        q19945E0
                        .black
                        2
                        q19945G
                        q19945E2
                        q19945_geometry
                        q19945_ready
                        q19945_stateInvariant
        dsimp only at hs
        rcases hs with hcpb | hterminal
        · exact q19945_post_not_cpb hcpb
        · exact
                hterminal
                        q19945M
                        q19945_new_member
                        q19945_fresh
                        q19945_not_old
                        q19945_history
                        q19945_bad
/-! -------------------------------------------------------------------------
        1. Exact live-row residual: selected endpoints only
------------------------------------------------------------------------- -/
/--
Everything off the selected pair is a literal ghostTokenAt frame.  Thus this
is the exact remaining live row after the cheap global adapter.
Truth split inside this Prop:
- fresh birth at the left endpoint;
- initiator c=1;
- initiator c>=2;
- responder c=-1;
- responder c<=-2;
- selected-owner stay.
The geometry premise is used only in the c=1 matching-comparison branch to
identify the responder with shiftRight b q.  A mismatch creates a leader and
therefore enters the CPB disjunct.
-/
def Lemma16PostEpochFreshSelectedLiveStepGeom : Prop :=
        forall {n psi kappa : Nat}
                (hpsi : 2 <= psi)
                (hn3 : 3 <= n)
                (ring : DirectedRing n)
                (Cepoch : Config n psi kappa)
                (epoch : Nat)
                (b k : Fin n)
                (kind : PPL.TokenKind)
                (step : Nat)
                (G : PPL.GhostConfig n psi kappa)
                (e : Fin n),
                Lemma16PostEpochFreshBorderGeometry ring b k psi ->
                DetectReadyCapped ring G.phys ->
                Lemma16PostEpochFreshStateInvariant
                        ring Cepoch epoch b k kind G ->
                let G' := PPL.ghostStep hpsi ring step G e
                Not (PPL.CPB ring G'.phys) ->
                forall (i : Fin n) (z : PPL.GhostToken n psi) (t : Nat),
                        Or (i = e) (i = ring.rightNeighbor e) ->
                        PPL.ghostTokenAt kind G' i = some z ->
                        z.lmeta.id = .born kind t ->
                        z.lmeta.birthSite = k ->
                        epoch <= t ->
                        Lemma16NoPriorCompletionId G' z.lmeta.id ->
                        exists q : Nat,
                                And (q < psi)
                                        (And
                                                (Lemma16FreshMacroStageAt ring k i z q)
                                                (And
                                                        (PPL.payloadCorrect ring Cepoch k q z.value)
                                                        (And
                                                                (Lemma16TargetPrefix ring Cepoch b k q)
                                                                (decodeOffset psi (tokenCode z.value) < 0 ->
                                                                        (Cepoch (shiftRight ring b q)).id =
                                                                                lemma16ExpectedAddOneBit
                                                                                        ring Cepoch k q))))
/--
Global live-step adapter.  Only the selected-pair residual above remains.
-/
theorem lemma16PostEpochFreshLiveStepGeom_of_selectedPair
        (hselected : Lemma16PostEpochFreshSelectedLiveStepGeom) :
        Lemma16PostEpochFreshLiveStepGeom := by
        unfold Lemma16PostEpochFreshSelectedLiveStepGeom at hselected
        unfold Lemma16PostEpochFreshLiveStepGeom
        intro n psi kappa hpsi hn3
        intro ring Cepoch epoch b k kind step G e
        intro hgeom hready hinv
        dsimp only
        by_cases hcpb :
                PPL.CPB ring
                        (PPL.ghostStep hpsi ring step G e).phys
        · exact Or.inl hcpb
        · apply Or.inr
          unfold Lemma16PostEpochFreshLiveInvariant
          intro i z t howner hid hsite hepoch hprior
          by_cases hie : i = e
          · exact
                hselected
                        hpsi hn3 ring Cepoch epoch b k kind step G e
                        hgeom hready hinv hcpb
                        i z t (Or.inl hie)
                        howner hid hsite hepoch hprior
          · by_cases hir : i = ring.rightNeighbor e
            · exact
                    hselected
                            hpsi hn3 ring Cepoch epoch b k kind step G e
                            hgeom hready hinv hcpb
                            i z t (Or.inr hir)
                            howner hid hsite hepoch hprior
            · have howner0 :
                    PPL.ghostTokenAt kind G i = some z := by
                    exact
                            (PPL.ghostTokenAt_ghostStep_frame
                                    hpsi ring step G e i kind hie hir).symm.trans
                                            howner
              have hprior0 :
                    Lemma16NoPriorCompletionId G z.lmeta.id := by
                    unfold Lemma16NoPriorCompletionId at hprior ⊢
                    intro m hm
                    apply hprior m
                    simp only [PPL.ghostStep, List.mem_append]
                    exact Or.inl (Or.inl hm)
              exact
                    hinv.2 i z t
                            howner0 hid hsite hepoch hprior0
/-! -------------------------------------------------------------------------
        1. Minimal semantic repair for the terminal row
------------------------------------------------------------------------- -/
/--
Canonical ghost states satisfy both facts:
- a born ID stored in a color slot has that same color;
- the timestamp encoded in the ID equals birthStep.
Neither fact is part of the arbitrary GhostConfig carrier.
-/
def Lemma16GhostLineageCoherent
        {n psi kappa : Nat}
        (G : PPL.GhostConfig n psi kappa) : Prop :=
        forall
                (slotKind bornKind : PPL.TokenKind)
                (i : Fin n)
                (z : PPL.GhostToken n psi)
                (t : Nat),
                PPL.ghostTokenAt slotKind G i = some z ->
                z.lmeta.id = .born bornKind t ->
                And
                        (slotKind = bornKind)
                        (z.lmeta.birthStep = t)
private theorem q19945_not_coherent :
        Not (Lemma16GhostLineageCoherent q19945G) := by
        intro hcoh
        have howner :
                PPL.ghostTokenAt .black q19945G q19945E2 =
                        some q19945Z := by
                simp [q19945G, PPL.ghostTokenAt]
        have h :=
                hcoh .black .black q19945E2 q19945Z 0
                        howner rfl
        have hbad : 1 = 0 := by
                simpa [q19945Z] using h.2
        omega
/--
This is the terminal row that should replace the false arbitrary-G version.
The extra coherence premise is exactly what lets the history bound on
birthStep feed the live-invariant gate on the timestamp t, and it rules out a
FreshCompletion of kind being emitted from the opposite color's done list.
-/
def Lemma16PostEpochFreshNewCompletionStepGeomCoherent : Prop :=
        forall {n psi kappa : Nat}
                (hpsi : 2 <= psi)
                (hn3 : 3 <= n)
                (ring : DirectedRing n)
                (Cepoch : Config n psi kappa)
                (epoch : Nat)
                (b k : Fin n)
                (kind : PPL.TokenKind)
                (step : Nat)
                (G : PPL.GhostConfig n psi kappa)
                (e : Fin n),
                Lemma16GhostLineageCoherent G ->
                Lemma16PostEpochFreshBorderGeometry ring b k psi ->
                DetectReadyCapped ring G.phys ->
                Lemma16PostEpochFreshStateInvariant
                        ring Cepoch epoch b k kind G ->
                let G' := PPL.ghostStep hpsi ring step G e
                Or
                        (PPL.CPB ring G'.phys)
                        (forall m : PPL.LineageMeta n,
                                m ∈ G'.completed ->
                                PPL.FreshCompletion (psi := psi) kind k m ->
                                m ∉ G.completed ->
                                (forall (i : Fin n) (z : PPL.GhostToken n psi) (t : Nat),
                                        PPL.ghostTokenAt kind G i = some z ->
                                        z.lmeta.id = .born kind t ->
                                        z.lmeta.birthSite = k ->
                                        epoch <= z.lmeta.birthStep) ->
                                Lemma16BadBorderWitness ring G.phys b k kind ->
                                False)
/--
Small canonical producer still needed by the architecture.
Truth argument: initialGhost has only initial IDs; birthGhost writes matching
slot color / ID color and birthStep=step; bumpTo changes only moves; setTwo
and liveShadow only route or retain metadata.
-/
def Lemma16GhostLineageCoherentRunProducer : Prop :=
        forall {n psi kappa : Nat}
                (hpsi : 2 <= psi)
                (ring : DirectedRing n)
                (C0 : Config n psi kappa)
                (pre : DetSchedule n),
                Lemma16GhostLineageCoherent
                        (PPL.ghostRun hpsi ring 0
                                (PPL.initialGhost C0) pre)
end PPL.Convergence.ReachCPB
#print axioms PPL.Convergence.ReachCPB.q19945_q19912_geometry_excluded
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeom_refuted
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshLiveStepGeom_of_selectedPair
