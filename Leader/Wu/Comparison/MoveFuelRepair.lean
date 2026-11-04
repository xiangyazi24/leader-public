import Leader.Wu.Comparison.PathStallRepair

/-!
# Non-refreshing transport fuel for comparison paths

Path-only stall expiration is locally correct but admits an exact moving-path
cycle: every SIGMOVE transfer refreshes the endpoint timer.  This separately
named physical repair adds one bounded `moveFuel : Fin (μ+1)` carried by a path.
Only an actual Algorithm-10 path transfer may change it.  A positive transfer
moves `fuel-1` to the receiver and leaves zero at the sender; an attempted
transfer at zero clears both local comparison carriers before CHECK.

All other stages preserve fuel literally.  Arbitrary initial fuel is permitted,
and no transition recharges it.  The result bounds transfer count for one
lineage; it does not bound scheduler time, choose a legitimate route budget, or
prove convergence.
-/

namespace PPLLMoveFuelComparisonRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair

/-! ## Fuel arithmetic -/

/-- Canonical zero in the nonempty fuel range. -/
def zeroMoveFuel (μ : Nat) : Fin (μ + 1) :=
  ⟨0, by omega⟩

/-- Spend one positive transfer unit. -/
def decMoveFuel (x : Fin (μ + 1)) (hx : x.val > 0) : Fin (μ + 1) :=
  ⟨x.val - 1, by omega⟩

/-- Every successful spend strictly lowers physical fuel. -/
theorem decMoveFuel_lt (x : Fin (μ + 1)) (hx : x.val > 0) :
    (decMoveFuel x hx).val < x.val := by
  simp [decMoveFuel]
  omega

/-- One abstract transfer attempt: zero is exhausted; positive fuel decrements. -/
def spendMoveFuel (x : Fin (μ + 1)) : Option (Fin (μ + 1)) :=
  if hzero : x.val = 0 then none
  else some (decMoveFuel x (Nat.pos_of_ne_zero hzero))

/-- Iterate abstract transfer attempts, keeping exhaustion absorbing. -/
def spendMoveFuelRun : Nat → Option (Fin (μ + 1)) → Option (Fin (μ + 1))
  | 0, x => x
  | _ + 1, none => none
  | k + 1, some x => spendMoveFuelRun k (spendMoveFuel x)

/-- A lineage is exhausted after `initial fuel + 1` attempted transfers. -/
theorem spendMoveFuelRun_clears (x : Fin (μ + 1)) :
    spendMoveFuelRun (x.val + 1) (some x) = none := by
  generalize hk : x.val = k
  induction k generalizing x with
  | zero =>
      simp [spendMoveFuelRun, spendMoveFuel, hk]
  | succ k ih =>
      have hpos : x.val > 0 := by omega
      let x' := decMoveFuel x hpos
      have hx' : x'.val = k := by
        dsimp [x', decMoveFuel]
        omega
      simp only [spendMoveFuelRun]
      have hnz : x.val ≠ 0 := by omega
      simp [spendMoveFuel, hnz]
      exact ih x' hx'

/-! ## Audit state and fail-closed SIGMOVE -/

/-- Authorized audit state plus an independently counted non-refreshing fuel. -/
structure MoveFuelAuthorizedAgentState (ψ μ : Nat) where
  core : AuthorizedAgentState ψ
  moveFuel : Fin (μ + 1)
  deriving DecidableEq, Repr

/-- Delete comparison/path controls without touching leader, bullet, reset, or
write machinery. -/
def clearAuditComparisonCarrier
    (u : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  let core := { u.core with state := .none }
  let core := { core with path := .bot }
  let core := { core with path2 := none }
  let core := { core with path4 := none, path5 := none }
  let core := { core with p := false, p_carry := false }
  ⟨core, false⟩

/-- Audit-level clearing preserves every declared numeric range. -/
theorem clearAuditComparisonCarrier_inProtocolDomain
    (u : AuthorizedAgentState ψ) (hu : u.core.inProtocolDomain κ) :
    (clearAuditComparisonCarrier u).core.inProtocolDomain κ := by
  unfold AgentState.inProtocolDomain at hu ⊢
  exact ⟨hu.1, trivial, trivial, hu.2.2.2.1, trivial, trivial⟩

/-- Lift any authorized stage while preserving each endpoint's fuel literally. -/
def keepFuel
    (f : AuthorizedAgentState ψ → AuthorizedAgentState ψ →
      AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    MoveFuelAuthorizedAgentState ψ μ × MoveFuelAuthorizedAgentState ψ μ :=
  let q := f l.core r.core
  (⟨q.1, l.moveFuel⟩, ⟨q.2, r.moveFuel⟩)

/-- Generic fuel-preserving lifts inherit core domain closure. -/
theorem keepFuel_inProtocolDomain
    (f : AuthorizedAgentState ψ → AuthorizedAgentState ψ →
      AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hf : let q := f l.core r.core
      q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ) :
    let q := keepFuel f l r
    q.1.core.core.inProtocolDomain κ ∧ q.2.core.core.inProtocolDomain κ := by
  exact hf

/-- Fuel-aware Algorithm 10.  The old authorized transition detects the actual
path transfer. Positive fuel moves and decrements; zero clears both post-SIGMOVE
comparison bundles before CHECK; no transfer preserves both fuels. -/
def moveFuelAuthorizedSigMove (hψ : ψ > 0)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    MoveFuelAuthorizedAgentState ψ μ × MoveFuelAuthorizedAgentState ψ μ :=
  let q := authorizedSigMove hψ l.core r.core
  if _hmoved : pathMovedRight l.core.core r.core.core q.1.core q.2.core = true then
    if hzero : l.moveFuel.val = 0 then
      (⟨clearAuditComparisonCarrier q.1, zeroMoveFuel μ⟩,
        ⟨clearAuditComparisonCarrier q.2, zeroMoveFuel μ⟩)
    else
      let nextFuel := decMoveFuel l.moveFuel (Nat.pos_of_ne_zero hzero)
      (⟨q.1, zeroMoveFuel μ⟩, ⟨q.2, nextFuel⟩)
  else
    (⟨q.1, l.moveFuel⟩, ⟨q.2, r.moveFuel⟩)

/-- Without a physical path transfer, neither endpoint fuel changes. -/
theorem moveFuelSigMove_no_transfer (hψ : ψ > 0)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hmove :
      let q := authorizedSigMove hψ l.core r.core
      pathMovedRight l.core.core r.core.core q.1.core q.2.core = false) :
    let q := moveFuelAuthorizedSigMove hψ l r
    q.1.moveFuel = l.moveFuel ∧ q.2.moveFuel = r.moveFuel := by
  simp [moveFuelAuthorizedSigMove, hmove]

/-- A positive transfer leaves no source fuel, overwrites receiver fuel with
`source-1`, and strictly decreases the moving lineage. -/
theorem moveFuelSigMove_positive_transfer (hψ : ψ > 0)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hmoved :
      let q := authorizedSigMove hψ l.core r.core
      pathMovedRight l.core.core r.core.core q.1.core q.2.core = true)
    (hpos : l.moveFuel.val > 0) :
    let q := moveFuelAuthorizedSigMove hψ l r
    q.1.moveFuel.val = 0 ∧
      q.2.moveFuel.val = l.moveFuel.val - 1 ∧
      q.2.moveFuel.val < l.moveFuel.val ∧
      q.1.core.core.path = .bot ∧ q.2.core.core.path = l.core.core.path := by
  change pathMovedRight l.core.core r.core.core
    (authorizedSigMove hψ l.core r.core).1.core
    (authorizedSigMove hψ l.core r.core).2.core = true at hmoved
  have hpath := hmoved
  simp [pathMovedRight] at hpath
  have hnz : l.moveFuel.val ≠ 0 := by omega
  simp [moveFuelAuthorizedSigMove, hmoved, hnz, zeroMoveFuel,
    decMoveFuel, hpath]
  omega

/-- A zero-fuel transfer attempt clears both local path/path2 bundles and both
permissions before CHECK can use the raw SIGMOVE output. -/
theorem moveFuelSigMove_zero_attempt_clears (hψ : ψ > 0)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hmoved :
      let q := authorizedSigMove hψ l.core r.core
      pathMovedRight l.core.core r.core.core q.1.core q.2.core = true)
    (hzero : l.moveFuel.val = 0) :
    let q := moveFuelAuthorizedSigMove hψ l r
    q.1.core.core.path = .bot ∧ q.2.core.core.path = .bot ∧
      q.1.core.core.path2 = none ∧ q.2.core.core.path2 = none ∧
      q.1.core.path0Crossed = false ∧ q.2.core.path0Crossed = false ∧
      q.1.moveFuel.val = 0 ∧ q.2.moveFuel.val = 0 := by
  change pathMovedRight l.core.core r.core.core
    (authorizedSigMove hψ l.core r.core).1.core
    (authorizedSigMove hψ l.core r.core).2.core = true at hmoved
  simp [moveFuelAuthorizedSigMove, hmoved, hzero,
    clearAuditComparisonCarrier, zeroMoveFuel]

/-- Fuel-aware SIGMOVE preserves the core numeric domain in all three branches. -/
theorem moveFuelAuthorizedSigMove_inProtocolDomain (hψ : ψ > 0)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hl : l.core.core.inProtocolDomain κ)
    (hr : r.core.core.inProtocolDomain κ) :
    let q := moveFuelAuthorizedSigMove hψ l r
    q.1.core.core.inProtocolDomain κ ∧ q.2.core.core.inProtocolDomain κ := by
  have hbase := authorizedSigMove_inProtocolDomain
    hψ l.core r.core hl hr
  unfold moveFuelAuthorizedSigMove
  dsimp only
  split
  · split
    · exact ⟨clearAuditComparisonCarrier_inProtocolDomain _ hbase.1,
        clearAuditComparisonCarrier_inProtocolDomain _ hbase.2⟩
    · exact hbase
  · exact hbase

/-! ## Full staged authorized repair -/

/-- Prefix through Algorithm 9, immediately before the specialized SIGMOVE. -/
def moveFuelBeforeSigMove (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    MoveFuelAuthorizedAgentState ψ μ × MoveFuelAuthorizedAgentState ψ μ :=
  let q := keepFuel (authorizedPPsi hψ) l r
  let q := keepFuel (authorizedGenSig hψ κ) q.1 q.2
  let q := keepFuel (authorizedCleanSig hψ) q.1 q.2
  keepFuel (authorizedEliminateSig hψ) q.1 q.2

/-- Prefix through fuel-aware SIGMOVE. -/
def moveFuelBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    MoveFuelAuthorizedAgentState ψ μ × MoveFuelAuthorizedAgentState ψ μ :=
  let q := moveFuelBeforeSigMove hψ κ l r
  moveFuelAuthorizedSigMove hψ q.1 q.2

/-- Complete authorized repair with fuel unchanged outside actual path transfer. -/
def moveFuelAuthorizedRepair (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    MoveFuelAuthorizedAgentState ψ μ × MoveFuelAuthorizedAgentState ψ μ :=
  let q := moveFuelBeforeCheck hψ κ l r
  let q := keepFuel (authorizedCheckSig hψ) q.1 q.2
  let q := keepFuel (authorizedDisappear hψ) q.1 q.2
  let q := keepFuel (authorizedCompareSig hψ) q.1 q.2
  let q := keepFuel (authorizedReconcile (suppressSig hψ)) q.1 q.2
  let q := keepFuel
    (authorizedReconcile (eliminateLeadersNoCollision hψ)) q.1 q.2
  keepFuel (authorizedReconcile (writeSeq hψ)) q.1 q.2

attribute [local irreducible] moveFuelBeforeSigMove moveFuelBeforeCheck

private theorem moveFuelBeforeSigMove_inProtocolDomain (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hl : l.core.core.inProtocolDomain κ)
    (hr : r.core.core.inProtocolDomain κ) :
    let q := moveFuelBeforeSigMove hψ κ l r
    q.1.core.core.inProtocolDomain κ ∧ q.2.core.core.inProtocolDomain κ := by
  unfold moveFuelBeforeSigMove
  dsimp only
  let q0 := keepFuel (authorizedPPsi hψ) l r
  have h0 := keepFuel_inProtocolDomain (authorizedPPsi hψ) l r
    (authorizedPPsi_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := keepFuel (authorizedGenSig hψ κ) q0.1 q0.2
  have h1 := keepFuel_inProtocolDomain (authorizedGenSig hψ κ) q0.1 q0.2
    (authorizedReconcile_inProtocolDomain (genSigSaturated hψ κ)
      q0.1.core q0.2.core
      (genSigSaturated_inProtocolDomain hψ q0.1.core.core q0.2.core.core
        h0.1 h0.2))
  let q2 := keepFuel (authorizedCleanSig hψ) q1.1 q1.2
  have h2 := keepFuel_inProtocolDomain (authorizedCleanSig hψ) q1.1 q1.2
    (authorizedReconcile_inProtocolDomain (cleanSig hψ) q1.1.core q1.2.core
      (cleanSig_inProtocolDomain hψ q1.1.core.core q1.2.core.core h1.1 h1.2))
  exact keepFuel_inProtocolDomain (authorizedEliminateSig hψ) q2.1 q2.2
    (authorizedReconcile_inProtocolDomain (eliminateSig hψ) q2.1.core q2.2.core
      (eliminateSig_inProtocolDomain hψ q2.1.core.core q2.2.core.core
        h2.1 h2.2))

private theorem moveFuelBeforeCheck_inProtocolDomain (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hl : l.core.core.inProtocolDomain κ)
    (hr : r.core.core.inProtocolDomain κ) :
    let q := moveFuelBeforeCheck hψ κ l r
    q.1.core.core.inProtocolDomain κ ∧ q.2.core.core.inProtocolDomain κ := by
  unfold moveFuelBeforeCheck
  dsimp only
  let q0 := moveFuelBeforeSigMove hψ κ l r
  have h0 := moveFuelBeforeSigMove_inProtocolDomain hψ κ l r hl hr
  exact moveFuelAuthorizedSigMove_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2

/-- Full move-fuel execution remains inside every core numeric range. -/
theorem moveFuelAuthorizedRepair_inProtocolDomain (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hl : l.core.core.inProtocolDomain κ)
    (hr : r.core.core.inProtocolDomain κ) :
    let q := moveFuelAuthorizedRepair hψ κ l r
    q.1.core.core.inProtocolDomain κ ∧ q.2.core.core.inProtocolDomain κ := by
  let q0 := moveFuelBeforeCheck hψ κ l r
  have h0 := moveFuelBeforeCheck_inProtocolDomain hψ κ l r hl hr
  let q1 := keepFuel (authorizedCheckSig hψ) q0.1 q0.2
  have h1 := keepFuel_inProtocolDomain (authorizedCheckSig hψ) q0.1 q0.2
    (authorizedReconcile_inProtocolDomain (checkSig hψ) q0.1.core q0.2.core
      (checkSig_inProtocolDomain hψ q0.1.core.core q0.2.core.core h0.1 h0.2))
  let q2 := keepFuel (authorizedDisappear hψ) q1.1 q1.2
  have h2 := keepFuel_inProtocolDomain (authorizedDisappear hψ) q1.1 q1.2
    (authorizedReconcile_inProtocolDomain (disappear hψ) q1.1.core q1.2.core
      (disappear_inProtocolDomain hψ q1.1.core.core q1.2.core.core h1.1 h1.2))
  let q3 := keepFuel (authorizedCompareSig hψ) q2.1 q2.2
  have h3 := keepFuel_inProtocolDomain (authorizedCompareSig hψ) q2.1 q2.2
    (authorizedCompareSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)
  let q4 := keepFuel (authorizedReconcile (suppressSig hψ)) q3.1 q3.2
  have h4 := keepFuel_inProtocolDomain
    (authorizedReconcile (suppressSig hψ)) q3.1 q3.2
    (authorizedReconcile_inProtocolDomain (suppressSig hψ) q3.1.core q3.2.core
      (suppressSig_inProtocolDomain hψ q3.1.core.core q3.2.core.core h3.1 h3.2))
  let q5 := keepFuel
    (authorizedReconcile (eliminateLeadersNoCollision hψ)) q4.1 q4.2
  have h5 := keepFuel_inProtocolDomain
    (authorizedReconcile (eliminateLeadersNoCollision hψ)) q4.1 q4.2
    (authorizedReconcile_inProtocolDomain (eliminateLeadersNoCollision hψ)
      q4.1.core q4.2.core
      (eliminateLeadersNoCollision_inProtocolDomain hψ
        q4.1.core.core q4.2.core.core h4.1 h4.2))
  exact keepFuel_inProtocolDomain
    (authorizedReconcile (writeSeq hψ)) q5.1 q5.2
    (authorizedReconcile_inProtocolDomain (writeSeq hψ) q5.1.core q5.2.core
      (writeSeq_inProtocolDomain hψ q5.1.core.core q5.2.core.core h5.1 h5.2))

/-! ## Finite bounded carrier and exact erasure -/

/-- Finite move-fuel state over the existing authorized bounded carrier. -/
structure MoveFuelBoundedAgentState (ψ κ μ : Nat) where
  core : AuthorizedBoundedAgentState ψ κ
  moveFuel : Fin (μ + 1)
  deriving DecidableEq, Repr

/-- Erase bounded payloads while retaining executable authorization and fuel. -/
def MoveFuelBoundedAgentState.erase
    (s : MoveFuelBoundedAgentState ψ κ μ) :
    MoveFuelAuthorizedAgentState ψ μ :=
  ⟨s.core.erase, s.moveFuel⟩

attribute [local irreducible] moveFuelAuthorizedRepair

/-- Total finite transition on move-fuel states. -/
def moveFuelBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelBoundedAgentState ψ κ μ) :
    MoveFuelBoundedAgentState ψ κ μ × MoveFuelBoundedAgentState ψ κ μ :=
  let q := moveFuelAuthorizedRepair hψ κ l.erase r.erase
  let hq := moveFuelAuthorizedRepair_inProtocolDomain hψ κ l.erase r.erase
    l.core.core.erase_inProtocolDomain r.core.core.erase_inProtocolDomain
  (⟨⟨BoundedAgentState.ofDomain q.1.core.core hq.1,
        q.1.core.path0Crossed⟩, q.1.moveFuel⟩,
    ⟨⟨BoundedAgentState.ofDomain q.2.core.core hq.2,
        q.2.core.path0Crossed⟩, q.2.moveFuel⟩)

/-- Finite execution erases exactly to the named move-fuel audit transition. -/
theorem erase_moveFuelBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelBoundedAgentState ψ κ μ) :
    let q := moveFuelBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) = moveFuelAuthorizedRepair hψ κ l.erase r.erase := by
  let q := moveFuelAuthorizedRepair hψ κ l.erase r.erase
  let hq := moveFuelAuthorizedRepair_inProtocolDomain hψ κ l.erase r.erase
    l.core.core.erase_inProtocolDomain r.core.core.erase_inProtocolDomain
  change (⟨⟨(BoundedAgentState.ofDomain q.1.core.core hq.1).erase,
      q.1.core.path0Crossed⟩, q.1.moveFuel⟩,
    ⟨⟨(BoundedAgentState.ofDomain q.2.core.core hq.2).erase,
      q.2.core.path0Crossed⟩, q.2.moveFuel⟩) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Packaged finite move-fuel protocol before timer composition. -/
def moveFuelBoundedProtocol (hψ : ψ > 0) (κ μ : Nat) : PopulationProtocol where
  Q := MoveFuelBoundedAgentState ψ κ μ
  Y := LeaderOutput
  transition := moveFuelBoundedTransition hψ κ
  output := fun s => if s.core.core.leader then .leader else .follower

/-- Constructive exhaustive certificate for the added fuel factor. -/
def moveFuelBoundedAgentState (ψ κ μ : Nat) :
    ExhaustiveList (MoveFuelBoundedAgentState ψ κ μ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (authorizedBoundedAgentState ψ κ)
      (ExhaustiveList.fin (μ + 1)))
    (fun x => ⟨x.1, x.2⟩)
    (by intro s; exact ⟨(s.core, s.moveFuel), rfl⟩)

/-- The move-fuel certificate is duplicate-free. -/
theorem moveFuelBoundedAgentState_values_nodup (ψ κ μ : Nat) :
    (moveFuelBoundedAgentState ψ κ μ).values.Nodup := by
  unfold moveFuelBoundedAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · apply ExhaustiveList.values_nodup_prod
    · exact authorizedBoundedAgentState_values_nodup ψ κ
    · exact ExhaustiveList.values_nodup_fin (μ + 1)
  · intro x y h
    rcases x with ⟨xc, xf⟩
    rcases y with ⟨yc, yf⟩
    cases h
    rfl

/-- Move fuel multiplies exact semantic cardinality by `μ+1`. -/
theorem moveFuelBoundedAgentState_values_length (ψ κ μ : Nat) :
    (moveFuelBoundedAgentState ψ κ μ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (μ + 1) := by
  unfold moveFuelBoundedAgentState ExhaustiveList.mapSurjective
  rw [List.length_map, ExhaustiveList.values_length_prod,
    authorizedBoundedAgentState_values_length, ExhaustiveList.values_length_fin]

/-- Every move-fuel state has an explicit finite index. -/
theorem moveFuelBoundedAgentState_decode_surjective (ψ κ μ : Nat) :
    Function.Surjective (moveFuelBoundedAgentState ψ κ μ).decode :=
  (moveFuelBoundedAgentState ψ κ μ).decode_surjective

/-- Exact finite-index representation of move-fuel states. -/
theorem moveFuelBoundedAgentState_decode_bijective (ψ κ μ : Nat) :
    Function.Injective (moveFuelBoundedAgentState ψ κ μ).decode ∧
      Function.Surjective (moveFuelBoundedAgentState ψ κ μ).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (moveFuelBoundedAgentState_values_nodup ψ κ μ),
    moveFuelBoundedAgentState_decode_surjective ψ κ μ⟩

end PPLLMoveFuelComparisonRepair
