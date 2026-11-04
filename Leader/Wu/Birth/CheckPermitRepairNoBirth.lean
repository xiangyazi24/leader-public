import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Birth.CheckChainRing
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor


/-!
# R1 no-birth words


This is the R1 analogue of `BirthShortDoneTerminalObserver.NoBirthAlong`.
The recursive premise is evaluated on the actual R1 successor after every
scheduler letter.


`birthEventR1` is the normalized-metadata newborn bit immediately before the
single `finalPhysical` tail.  `rowBirthEventR1` separately records a visible
follower-to-leader change after the complete row.
-/


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B10NoBirthR1


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC
  K2BirthLeaderNormalize
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
  BirthShortDoneTerminalHost


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthCheckPermitRepairLeaf.FC n psi kappa tau


/-- R1 metadata after bounded reification, the two expiry calls, and endpoint
leader normalization; this is exactly the pair fed to `finalPhysical`. -/
def metadataR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r
  (normalizeLeader hpsi q.1, normalizeLeader hpsi q.2)


/-- Cut-level R1 birth event: an original follower is a leader in normalized
metadata, immediately before newborn initialization and collision/K2. -/
def birthEventR1Cut
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Bool :=
  let q := metadataR1 hpsi h2 l r
  newborn l q.1 || newborn r q.2


/-- The B10 event is the exact R1 metadata event. -/
def birthEventR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Bool :=
  birthEventR1Cut hpsi h2 l r


/-- Completed-row follower-to-leader observation.  This is useful for audits,
but `NoBirthAlongR1` uses the stronger metadata event above. -/
def rowBirthEventR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Bool :=
  let q := BirthCheckPermitRepair.row
    hpsi (by decide : 0 < 2) h2 l r
  newborn l q.1 || newborn r q.2


/-- The executable R1 row is one `finalPhysical` call on `metadataR1`. -/
theorem row_eq_finalPhysical_metadataR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r =
      let q := metadataR1 hpsi h2 l r
      finalPhysical hpsi l r q.1 q.2 := by
  rfl


/-! ## The final tail cannot create a leader -/


private theorem expiringK2_no_new_leaders
    (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ((ExpiringK2Projection.row hpsi l r).1.core.core.leader = true →
      l.core.core.leader = true) ∧
    ((ExpiringK2Projection.row hpsi l r).2.core.core.leader = true →
      r.core.core.leader = true) := by
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
    (by decide : 0 < 1) (observeCell l) (observeCell r)
  constructor
  · intro hout
    cases hl : l.core.core.leader with
    | false =>
        have hlf : (observeCell l).leader = false := hl
        have hf := hk.1 hlf
        have he := congrArg
          (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
        change (ExpiringK2Projection.row hpsi l r).1.core.core.leader =
          (sinkKernelC (by decide) (observeCell l) (observeCell r)).1.leader at he
        have hz := he.trans hf
        simp_all
    | true => rfl
  · intro hout
    cases hr : r.core.core.leader with
    | false =>
        have hrf : (observeCell r).leader = false := hr
        have hf := hk.2 hrf
        have he := congrArg
          (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
        change (ExpiringK2Projection.row hpsi l r).2.core.core.leader =
          (sinkKernelC (by decide) (observeCell l) (observeCell r)).2.leader at he
        have hz := he.trans hf
        simp_all
    | true => rfl


private theorem collisionRow_no_new_leaders
    (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ((collisionRow hpsi l r).1.core.core.leader = true →
      l.core.core.leader = true) ∧
    ((collisionRow hpsi l r).2.core.core.leader = true →
      r.core.core.leader = true) := by
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · exact ⟨fun _ => hb.1, fun _ => hb.2⟩
  · rw [collisionRow_of_not_both hpsi l r hb]
    exact expiringK2_no_new_leaders hpsi l r


private theorem finalPhysical_no_new_leaders
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) :
    ((finalPhysical hpsi oldL oldR metaL metaR).1.core.core.leader = true →
      metaL.core.core.leader = true) ∧
    ((finalPhysical hpsi oldL oldR metaL metaR).2.core.core.leader = true →
      metaR.core.core.leader = true) := by
  unfold finalPhysical
  have h := collisionRow_no_new_leaders hpsi
    (initializeNewborn oldL metaL) (initializeNewborn oldR metaR)
  exact
    ⟨fun hout =>
        (initializeNewborn_leader oldL metaL).symm.trans (h.1 hout),
      fun hout =>
        (initializeNewborn_leader oldR metaR).symm.trans (h.2 hout)⟩


private theorem old_leader_of_newborn_false
    (old out : ExpiringAgentState psi kappa tau)
    (hn : newborn old out = false)
    (hout : out.core.core.leader = true) :
    old.core.core.leader = true := by
  cases h : old.core.core.leader with
  | false =>
      simp [newborn, h, hout] at hn
  | true => rfl


/-- A false metadata birth event guarantees that the complete R1 row creates
no leader.  Existing leaders may nevertheless be deleted by the final
collision/K2 elimination tail. -/
theorem row_no_new_leader_of_birthEventR1_false
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hn : birthEventR1 hpsi h2 l r = false) :
    ((BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = true →
      l.core.core.leader = true) ∧
    ((BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = true →
      r.core.core.leader = true) := by
  have hnb :
      newborn l (metadataR1 hpsi h2 l r).1 = false ∧
      newborn r (metadataR1 hpsi h2 l r).2 = false := by
    simpa only [birthEventR1, birthEventR1Cut, Bool.or_eq_false_iff] using hn
  rw [row_eq_finalPhysical_metadataR1 hpsi h2 l r]
  dsimp only
  have ht := finalPhysical_no_new_leaders hpsi l r
    (metadataR1 hpsi h2 l r).1 (metadataR1 hpsi h2 l r).2
  exact
    ⟨fun hout => old_leader_of_newborn_false
        l (metadataR1 hpsi h2 l r).1 hnb.1 (ht.1 hout),
      fun hout => old_leader_of_newborn_false
        r (metadataR1 hpsi h2 l r).2 hnb.2 (ht.2 hout)⟩


/-- Whole-ring one-step form, including the aliased-edge convention. -/
theorem step1_no_new_leader_of_birthEventR1_false
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (e : Fin n)
    (hn : birthEventR1 hpsi h2
      (C e) (C (ring.rightNeighbor e)) = false)
    (i : Fin n)
    (hout : (step1 hpsi h2 ring C e i).core.core.leader = true) :
    (C i).core.core.leader = true := by
  have hrow := row_no_new_leader_of_birthEventR1_false
    hpsi h2 (C e) (C (ring.rightNeighbor e)) hn
  by_cases hie : i = e
  · subst i
    rw [BirthCheckChainR1Ring.step1_left hpsi h2 ring C e] at hout
    exact hrow.1 hout
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hne : ring.rightNeighbor e ≠ e := hie
      rw [BirthCheckChainR1Ring.step1_right hpsi h2 ring C e hne] at hout
      exact hrow.2 hout
    · rw [BirthCheckPermitRepairLeaf.step1_other
        hpsi h2 ring C e i hie hir] at hout
      exact hout


/-! ## Recursive actual-successor no-birth words -/


/-- No R1 metadata birth at any letter, recursively evaluated on the actual
R1 successor configuration. -/
def NoBirthAlongR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlongR1 hpsi h2 ring (step1 hpsi h2 ring C e) es


/-- Concatenation uses the actual R1 state after the first word. -/
theorem noBirthAlongR1_append
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (u v : List (Fin n)) :
    NoBirthAlongR1 hpsi h2 ring C (u ++ v) ↔
      NoBirthAlongR1 hpsi h2 ring C u ∧
      NoBirthAlongR1 hpsi h2 ring
        (u.foldl (step1 hpsi h2 ring) C) v := by
  induction u generalizing C with
  | nil =>
      simp only [List.nil_append, List.foldl_nil, NoBirthAlongR1, true_and]
  | cons e u ih =>
      simp only [List.cons_append, List.foldl_cons, NoBirthAlongR1]
      rw [ih]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩


/-- Every prefix of an R1 no-birth word is again an R1 no-birth word. -/
theorem noBirthAlongR1_take
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (es : List (Fin n))
    (hn : NoBirthAlongR1 hpsi h2 ring C es) (t : Nat) :
    NoBirthAlongR1 hpsi h2 ring C (es.take t) := by
  induction t generalizing C es with
  | zero => trivial
  | succ t ih =>
      cases es with
      | nil => trivial
      | cons e es => exact ⟨hn.1, ih _ _ hn.2⟩


/-- Historical name retained from the requested interface: this proves
antitonicity, not equality of leader sets.  No follower can become a leader;
an existing leader may be eliminated. -/
theorem leaders_const_of_noBirthAlongR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : FC n psi kappa tau),
      NoBirthAlongR1 hpsi h2 ring C w →
      ∀ i : Fin n,
        ((w.foldl (step1 hpsi h2 ring) C) i).core.core.leader = true →
          (C i).core.core.leader = true := by
  induction w with
  | nil =>
      intro C _ i hi
      exact hi
  | cons e w ih =>
      intro C hn i hout
      simp only [List.foldl_cons] at hout
      have hmid :
          (step1 hpsi h2 ring C e i).core.core.leader = true :=
        ih (step1 hpsi h2 ring C e) hn.2 i hout
      exact step1_no_new_leader_of_birthEventR1_false
        hpsi h2 ring C e hn.1 i hmid


-- END PART 1
/-! ## Transfer from the terminal consumer away from class E -/


section ConsumerAgree
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepPreCheckResetRepair
  K2BirthDispatcher K2BirthDispatcherDone BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHost BirthSigMoveDisposalRepair


private theorem r1_expiring_eq_consumer_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    BirthCheckPermitRepair.expiring
        hpsi (by decide : 0 < 2) h2 l r =
      doneMetadataEntryWidth
        hpsi (by decide : 0 < 2) h2 l r := by
  have ha := BirthCheckPermitRepairAgree.authorized_eq hpsi h2
    (prepareExpiringDisposal hpsi l).core.erase
    (prepareExpiringDisposal hpsi r).core.erase h
  have hb :
      BirthCheckPermitRepair.bounded hpsi (by decide : 0 < 2) h2
          (prepareExpiringDisposal hpsi l).core
          (prepareExpiringDisposal hpsi r).core =
        doneMetadataBoundedEntryWidth
          hpsi (by decide : 0 < 2) h2
          (prepareExpiringDisposal hpsi l).core
          (prepareExpiringDisposal hpsi r).core := by
    unfold BirthCheckPermitRepair.bounded doneMetadataBoundedEntryWidth
    dsimp only
    exact BirthCheckPermitRepairAgree.reify_congr ha
      (BirthCheckPermitRepair.authorized_domain
        hpsi (by decide : 0 < 2) h2 _ _
        (prepareExpiringDisposal hpsi l).core.core.erase_inProtocolDomain
        (prepareExpiringDisposal hpsi r).core.core.erase_inProtocolDomain)
      (doneMetadataAuthorizedEntryWidth_domain
        hpsi (by decide : 0 < 2) h2 _ _
        (prepareExpiringDisposal hpsi l).core.core.erase_inProtocolDomain
        (prepareExpiringDisposal hpsi r).core.core.erase_inProtocolDomain)
  unfold BirthCheckPermitRepair.expiring doneMetadataEntryWidth
  simp only [hb]


/-- Outside class E, normalized R1 metadata is exactly consumer metadata. -/
theorem metadataR1_eq_consumer_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    metadataR1 hpsi h2 l r =
      BirthShortDoneTerminalHost.metadata
        hpsi (by decide : 0 < 2) h2 l r := by
  unfold metadataR1 BirthShortDoneTerminalHost.metadata
  dsimp only
  rw [r1_expiring_eq_consumer_of_no_equal hpsi h2 l r h]
end ConsumerAgree


/-- Hence the cut-level birth event itself transfers, not merely the completed
row, on every non-E pair. -/
theorem birthEventR1_eq_consumer_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    birthEventR1 hpsi h2 l r =
      BirthShortDoneTerminalObserver.birthEvent
        hpsi (by decide : 0 < 2) h2 l r := by
  have hm := metadataR1_eq_consumer_of_no_equal hpsi h2 l r h
  unfold birthEventR1 birthEventR1Cut
    BirthShortDoneTerminalObserver.birthEvent
  rw [hm]


/-- Consumer no-birth transfers letter-for-letter on `NoEqualAlong` words.
The recursive `NoEqualAlong` state is the consumer successor; `step1_eq`
identifies the actual R1 successor with it at each induction step. -/
theorem noBirthAlongR1_of_consumer_noEqual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ (C : FC n psi kappa tau),
      BirthShortDoneTerminalObserver.NoBirthAlong
          hpsi (by decide : 0 < 2) h2 ring C w →
      BirthCheckPermitRepairAgree.NoEqualAlong hpsi h2 ring C w →
      NoBirthAlongR1 hpsi h2 ring C w := by
  induction w with
  | nil =>
      intro C _ _
      trivial
  | cons e w ih =>
      intro C hnb hne
      have he :=
        (BirthCheckPermitRepairAgree.noEqualAlong_cons
          hpsi h2 ring C e w).1 hne
      constructor
      · rw [birthEventR1_eq_consumer_of_no_equal
          hpsi h2 (C e) (C (ring.rightNeighbor e)) he.1]
        exact hnb.1
      · have hs := BirthCheckPermitRepairAgree.step1_eq
          hpsi h2 ring C e he.1
        have hnbTail :
            BirthShortDoneTerminalObserver.NoBirthAlong
              hpsi (by decide : 0 < 2) h2 ring
              (BirthPhaseWait2BlockProgress.currentStep2
                hpsi h2 ring C e) w := by
          simpa only [BirthPhaseWait2BlockProgress.currentStep2] using hnb.2
        rw [hs]
        exact ih _ hnbTail he.2


/-- Packaged transfer requested by B10: no-birth and exact final run agreement
hold simultaneously on the same original scheduler word. -/
theorem consumer_noBirth_transfer_of_noEqual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n))
    (hnb : BirthShortDoneTerminalObserver.NoBirthAlong
      hpsi (by decide : 0 < 2) h2 ring C w)
    (hne : BirthCheckPermitRepairAgree.NoEqualAlong
      hpsi h2 ring C w) :
    NoBirthAlongR1 hpsi h2 ring C w ∧
      w.foldl (step1 hpsi h2 ring) C =
        w.foldl
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C := by
  exact
    ⟨noBirthAlongR1_of_consumer_noEqual hpsi h2 ring w C hnb hne,
      BirthCheckPermitRepairAgree.run_eq hpsi h2 ring w C hne⟩


/-! ## Two exact producer interfaces below stepFinal -/


/-- A current-state certificate strong enough to produce no-birth on every
R1 word: it is closed under the actual successor and blocks the next R1 event. -/
structure ClosedNoBirthR1Certificate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (Safe : FC n psi kappa tau → Prop) : Prop where
  event_false :
    ∀ C e, Safe C →
      birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false
  closed :
    ∀ C e, Safe C → Safe (step1 hpsi h2 ring C e)


/-- A closed current-state R1 certificate really does produce the recursive
no-birth premise for every finite word. -/
theorem noBirthAlongR1_of_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (Safe : FC n psi kappa tau → Prop)
    (cert : ClosedNoBirthR1Certificate hpsi h2 ring Safe)
    (w : List (Fin n)) (C : FC n psi kappa tau)
    (hC : Safe C) :
    NoBirthAlongR1 hpsi h2 ring C w := by
  induction w generalizing C with
  | nil => trivial
  | cons e w ih =>
      exact
        ⟨cert.event_false C e hC,
          ih (step1 hpsi h2 ring C e) (cert.closed C e hC)⟩


/-- Prefix-decomposable load safety on the actual R1 run. -/
def LoadSafeAlongR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (LoadSafeAt : FC n psi kappa tau → Fin n → Prop)
    (C : FC n psi kappa tau) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      LoadSafeAt C e ∧
      LoadSafeAlongR1 hpsi h2 ring LoadSafeAt
        (step1 hpsi h2 ring C e) es


/-- Any prefix-decomposable load contract whose one-letter clause blocks the
actual R1 event is a B10 no-birth producer. -/
theorem noBirthAlongR1_of_loadSafe
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (LoadSafeAt : FC n psi kappa tau → Fin n → Prop)
    (hAt : ∀ C e, LoadSafeAt C e →
      birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false)
    (w : List (Fin n)) (C : FC n psi kappa tau)
    (hload : LoadSafeAlongR1 hpsi h2 ring LoadSafeAt C w) :
    NoBirthAlongR1 hpsi h2 ring C w := by
  induction w generalizing C with
  | nil => trivial
  | cons e w ih =>
      exact
        ⟨hAt C e hload.1,
          ih (step1 hpsi h2 ring C e) hload.2⟩


/-!
PLAN — B10 producer on the frozen final step.


The theorem still missing from the repository is not another recursive
observer lemma.  It is a producer/mass theorem for the actual host-parametric
B9+R1 `stepFinal`.


Once `B9SpliceTableHost` (or its successor) is committed and the final carrier
is fixed, define the physical projection `eraseFinal` and the actual physical
subword `physWordFinal C w`, following the *real successive `stepFinal` states*.
The target event should be something of the following shape:


```
def FinalNoBirthR1Word
    (C : FinalConfig n psi kappa tau) (w : List (Fin n)) : Prop :=
  NoBirthAlongR1 hpsi h2 ring (eraseFinal C) (physWordFinal C w)


-- B10/B11 boundary, schematic only:
theorem b10_noBirthR1_mass_stepFinal :
  ∀ C, PostBirthSafeFinal C →
    n ^ B ≤ Q * FixedSpanRenewalPayload.wordSum n B
      (fun w => if FinalNoBirthR1Word C w then 1 else 0)
```


A CLOSED-certificate route must supply, on the same `stepFinal`:


1. `PostBirthSafeFinal` is one-step closed under every controller service.
2. Every physical service projects to exactly one R1 `step1` service on the
   current projected configuration (including class E).
3. At every projected physical service from a safe state, `birthEventR1` is
   false; the R1 source-exclusion proof may use the label frames exported by
   `B6LocalRuler` / `B6LocalRulerE`, but must also close CHECK/provenance,
   writer, disposal and expiry premises.
4. Every nonphysical B9 service preserves the certificate and cannot forge a
   physical leader outside the R1 event accounting.
5. `physWordFinal` is defined recursively from actual successors, not from a
   retrospectively chosen host schedule.


A LOAD-SAFE route may replace (1)--(4) by an actual prefix-decomposable
`LoadSafeAlongFinal`: its one-letter clause must imply the R1 event is false,
and its tail premise must be re-established on the actual next `stepFinal`
state.  B11 then has to bound the mass of those words on the ORIGINAL uniform
controller scheduler.  It is not sound to assume that the extracted physical
subword is uniformly distributed, and one isolated successful no-birth word is
not the required B10/B11 producer.
-/


end B10NoBirthR1
