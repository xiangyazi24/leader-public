import Leader.L3.Grant.BlockFrozenRecovery

/-!
G16 C.17. CANONICAL one-service grant/latch bridge.

All agents of grantBlockFrozenColdEmbedConfig, including every
exterior site, are made from Agent.blank. Consequently no OLD
request, grant or native leader can migrate, FIRE, or veto T2
on this one service. This is false for arbitrary cold scratch:
see resetColdForeignPairRow and grantBlockNativeVetoSamePair.

The new theorem proves latch iff physical-root-grant and
closes the three-way one-edge Bellman row cover for the actual
canonical carrier. It does not prove the separate G13 frozen
MASS/renewal-window estimate, which requires multi-step first-hit
and C.2 renewal coupling.  core Lean 4.33.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
set_option autoImplicit false
set_option Elab.async false

/-- A field of a dependent if is the common value of both branches. -/
private theorem grantBlockFrozenLatchDiteField {α β : Type}
    {P : Prop} [Decidable P] (f : α → β)
    {a : P → α} {b : ¬ P → α} {v : β}
    (ha : ∀ h, f (a h) = v) (hb : ∀ h, f (b h) = v) :
    f (dite P a b) = v := by
  by_cases h : P
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

/-- A field of an if, branch by branch. -/
private theorem grantBlockFrozenLatchIteField {α β : Type}
    {P : Prop} [Decidable P] (f : α → β)
    {a b : α} {v : β}
    (ha : P → f a = v) (hb : ¬ P → f b = v) :
    f (if P then a else b) = v := by
  by_cases h : P
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- The canonical old full-state has no request tokens.
Consumer: the T0/T2 grant-event source in C.17. -/
theorem grantBlockFrozenLatchEmbedNoRequests
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (i : Fin n) :
    (grantBlockFrozenColdEmbedConfig ring C root S i).req =
      false := by
  exact grantBlockFrozenLatchDiteField Agent.req
    (fun _ => rfl) (fun _ => rfl)

/-- The canonical old full-state has no native leader, even
at its unprotected exterior sites. Consumer: exclusion of the
T1 native-sink BANK producer veto. -/
theorem grantBlockFrozenLatchEmbedNoLeaders
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (i : Fin n) :
    (grantBlockFrozenColdEmbedConfig ring C root S i).l =
      false := by
  exact grantBlockFrozenLatchDiteField Agent.l
    (fun _ => rfl) (fun _ => rfl)

/-- Native E cannot manufacture a leader from two old
leaderless agents. Consumer: literal full Base token owner. -/
private theorem grantBlockFrozenLatchNativeLeaderless
    {c : Compiled} (x y : Agent c)
    (hx : x.l = false) (hy : y.l = false) :
    (certLiteralEPair x.certNative y.certNative).1.l = false ∧
    (certLiteralEPair x.certNative y.certNative).2.l = false := by
  simp [certLiteralEPair, Agent.certNative, hx, hy]
  repeat' (first | rfl | split)

/-- Neither physical OLD grant is present, hence FIRE cannot
consume a newly produced BANK grant on this same step.
Consumer: C.17 token-owner exclusivity. -/
private theorem grantBlockFrozenLatchNoFire
    {c : Compiled} (x y : Agent c) (fX fY : CertNative)
    (hx : x.grant = false) (hy : y.grant = false) :
    fireSelect x y fX fY = none := by
  cases hrx : x.req <;>
    cases hry : y.req <;>
    simp [fireSelect, hx, hy, hrx, hry]

/-- Under no old grants, no FIRE, and no final native leaders,
the literal tokenStep source grant is precisely BANK success;
the responder cannot gain a grant. DCC request is arbitrary.
Consumer: both directions of the canonical latch event. -/
private theorem grantBlockFrozenLatchTokenRow
    {c : Compiled} (x y : Agent c) (fX fY : CertNative)
    (dcc success : Bool)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfx : fX.l = false) (hfy : fY.l = false) :
    (tokenStep x y fX fY none dcc success).1.grant =
      success ∧
    (tokenStep x y fX fY none dcc success).2.1.grant =
      false := by
  cases hrx : x.req <;>
    cases hry : y.req <;>
    cases dcc <;>
    cases success <;>
    simp [tokenStep, hx, hy, hfx, hfy, hrx, hry] <;>
    (repeat' (first | rfl | split))

/-- The real BASE owner in the spatial branch, including the
complete token producer, has grant outputs (BANK success,false).
No claim is made about arbitrary old grants or final leaders.
Consumer: the composed protocol transition projection. -/
private theorem grantBlockFrozenLatchBaseGrant
    {c : Compiled} (ev : CertEvent) (x y : Agent c)
    (hsp : c.useSmall = false)
    (hlx : x.l = false) (hly : y.l = false)
    (hgX : x.grant = false) (hgY : y.grant = false) :
    (baseStep c ev x y).1.grant =
      bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b ∧
    (baseStep c ev x y).2.grant = false := by
  have hnative :=
    grantBlockFrozenLatchNativeLeaderless x y hlx hly
  have hfire := grantBlockFrozenLatchNoFire x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    hgX hgY
  have htoken := grantBlockFrozenLatchTokenRow
    x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y ev).request
    (bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b)
    hgX hgY hnative.1 hnative.2
  simpa [baseStep, hsp, hfire, fireAtSite,
    Agent.setNative, Agent.setCPriv, copyBank,
    hnative.1, hnative.2] using htoken

/-- The complete three-owner protocol writes grant only from
the BASE owner. Thus its source grant is OLD bankSuccess and
its responder grant is false on an all-blank-token pair.
Consumer: the physical root grant at a selected edge. -/
theorem grantBlockFrozenLatchTransitionGrant
    {c : Compiled} (x y : Agent c)
    (hsp : c.useSmall = false)
    (hlx : x.l = false) (hly : y.l = false)
    (hgX : x.grant = false) (hgY : y.grant = false) :
    (transition c x y).1.grant =
      bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b ∧
    (transition c x y).2.grant = false := by
  change
    (baseStep c (certificateStep c x y).2.2 x y).1.grant =
      bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b ∧
    (baseStep c (certificateStep c x y).2.2 x y).2.grant =
      false
  exact grantBlockFrozenLatchBaseGrant
    (certificateStep c x y).2.2 x y
    hsp hlx hly hgX hgY

/-- The actual full protocol's new root grant bit, for ANY
scheduler letter, equals the nominated root's old BANK success
event on the reconstructed canonical configuration. If the root
is the responder or a third site it remains grant-free.
Consumer: G16 C.17 latch-real-grant equivalence. -/
theorem grantBlockFrozenLatchCanonicalRootGrant
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring
      (grantBlockFrozenColdEmbedConfig ring C root S) e)
      root).grant =
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root
        (grantBlockFrozenColdEmbedConfig ring C root S) e := by
  have hpair := grantBlockFrozenLatchTransitionGrant
    (grantBlockFrozenColdEmbedConfig ring C root S e)
    (grantBlockFrozenColdEmbedConfig ring C root S
      (ring.rightNeighbor e))
    hsp
    (grantBlockFrozenLatchEmbedNoLeaders ring C root S e)
    (grantBlockFrozenLatchEmbedNoLeaders ring C root S
      (ring.rightNeighbor e))
    (grantBlockFrozenColdEmbedNoGrants ring C root S e)
    (grantBlockFrozenColdEmbedNoGrants ring C root S
      (ring.rightNeighbor e))
  by_cases he : e = root
  · subst e
    change
      (if root = root then
        (transition (compileAdvice q)
          (grantBlockFrozenColdEmbedConfig ring C root S root)
          (grantBlockFrozenColdEmbedConfig ring C root S
            (ring.rightNeighbor root))).1
       else if root = ring.rightNeighbor root then
        (transition (compileAdvice q)
          (grantBlockFrozenColdEmbedConfig ring C root S root)
          (grantBlockFrozenColdEmbedConfig ring C root S
            (ring.rightNeighbor root))).2
       else grantBlockFrozenColdEmbedConfig ring C root S root).grant =
      (if root = root then
        bankSuccess
          (bankCell
            (grantBlockFrozenColdEmbedConfig ring C root S root)
            (grantBlockFrozenColdEmbedConfig ring C root S root).pack.val)
          (bankCell
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor root))
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor root)).pack.val)
          (packNext
            (grantBlockFrozenColdEmbedConfig ring C root S root).pack.val
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor root)).pack.val
            (compileAdvice q).b) (compileAdvice q).b
       else false)
    rw [if_pos rfl, if_pos rfl]
    exact hpair.1
  · have hn : root ≠ e := Ne.symm he
    change
      (if root = e then
        (transition (compileAdvice q)
          (grantBlockFrozenColdEmbedConfig ring C root S e)
          (grantBlockFrozenColdEmbedConfig ring C root S
            (ring.rightNeighbor e))).1
       else if root = ring.rightNeighbor e then
        (transition (compileAdvice q)
          (grantBlockFrozenColdEmbedConfig ring C root S e)
          (grantBlockFrozenColdEmbedConfig ring C root S
            (ring.rightNeighbor e))).2
       else grantBlockFrozenColdEmbedConfig ring C root S root).grant =
      (if e = root then
        bankSuccess
          (bankCell
            (grantBlockFrozenColdEmbedConfig ring C root S e)
            (grantBlockFrozenColdEmbedConfig ring C root S e).pack.val)
          (bankCell
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor e))
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor e)).pack.val)
          (packNext
            (grantBlockFrozenColdEmbedConfig ring C root S e).pack.val
            (grantBlockFrozenColdEmbedConfig ring C root S
              (ring.rightNeighbor e)).pack.val
            (compileAdvice q).b) (compileAdvice q).b
       else false)
    rw [if_neg hn, if_neg he]
    exact grantBlockFrozenLatchIteField Agent.grant
      (fun _ => hpair.2)
      (fun _ => grantBlockFrozenColdEmbedNoGrants ring C root S root)

/-- One-service Boolean EQUALITY, hence both implications:
the canonical reference's OLD success latch is true exactly
when the REAL full-protocol successor first grants its root.
The two old configurations being compared are identical on
PACK/four-field positions and blank outside.
Consumer: C.3 covered row classification. -/
theorem grantBlockFrozenLatchCanonicalEvent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (hbound : GrantBlockFrozenColdLeaseBound
      (ceilLogTwo n) S)
    (hfalse : S.success = false)
    (e : Fin n) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root S e).success =
    (((protocol (ceilLogTwo n)).step ring
      (grantBlockFrozenColdEmbedCarrier ring C root
        hbuffered.1 S).val e) root).grant := by
  have hstep := grantBlockFrozenColdEmbedOneStepFields
    ring C root radius hsp hbuffered S hbound hfalse e
  have hreal := grantBlockFrozenLatchCanonicalRootGrant
    ring C root e S hsp
  change
    (((protocol (ceilLogTwo n)).step ring
      (grantBlockFrozenColdEmbedCarrier ring C root
        hbuffered.1 S).val e) root).grant =
      GrantBankReference.bankLocalReferenceRealSuccessEvent
        ring root
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val e at hreal
  exact hstep.2.2.trans hreal.symm

/-- Every edge of a canonical buffered carrier has one of
the THREE real C.3 rows (RESET, active grant-free/non-RESET,
or matched physical grant and local success). No hrows is
assumed. Consumer: statewise local Bellman transfer. -/
theorem grantBlockFrozenLatchCanonicalRows
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (hbound : GrantBlockFrozenColdLeaseBound
      (ceilLogTwo n) S)
    (hfalse : S.success = false) :
    ∀ edge : Fin n,
      (((protocol (ceilLogTwo n)).step ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val edge) root).mode = .RESET ∨
      (Counter.GrantFree
          ((protocol (ceilLogTwo n)).step ring
            (grantBlockFrozenColdEmbedCarrier ring C root
              hbuffered.1 S).val edge) root ∧
       (((protocol (ceilLogTwo n)).step ring
         (grantBlockFrozenColdEmbedCarrier ring C root
           hbuffered.1 S).val edge) root).mode ≠ .RESET ∧
       (GrantBankReference.bankLocalReferenceStepClamped
         ring root S edge).success = false) ∨
      (¬ Counter.GrantFree
         ((protocol (ceilLogTwo n)).step ring
           (grantBlockFrozenColdEmbedCarrier ring C root
             hbuffered.1 S).val edge) root ∧
       (GrantBankReference.bankLocalReferenceStepClamped
         ring root S edge).success = true) := by
  intro edge
  have heq := grantBlockFrozenLatchCanonicalEvent
    ring C root radius hsp hbuffered S hbound hfalse edge
  by_cases hreset :
      (((protocol (ceilLogTwo n)).step ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val edge) root).mode = .RESET
  · exact Or.inl hreset
  · by_cases hgrant :
      (((protocol (ceilLogTwo n)).step ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val edge) root).grant = false
    · exact Or.inr (Or.inl ⟨hgrant, hreset,
        heq.trans hgrant⟩)
    · have hgtrue :
          (((protocol (ceilLogTwo n)).step ring
            (grantBlockFrozenColdEmbedCarrier ring C root
              hbuffered.1 S).val edge) root).grant = true := by
        cases hh :
            (((protocol (ceilLogTwo n)).step ring
              (grantBlockFrozenColdEmbedCarrier ring C root
                hbuffered.1 S).val edge) root).grant with
        | false => exact False.elim (hgrant hh)
        | true => rfl
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · intro hfree
        change
          (((protocol (ceilLogTwo n)).step ring
            (grantBlockFrozenColdEmbedCarrier ring C root
              hbuffered.1 S).val edge) root).grant = false
          at hfree
        rw [hgtrue] at hfree
        cases hfree
      · exact heq.trans hgtrue

/-- C.3 state-uniform local all-edges Bellman inequality for
every physically representable UNLATCHED frozen reference at
a buffered PACK entrance.  hrows is derived, not assumed.
Consumer: the still-open frozen G13 renewal/mass producer. -/
theorem grantBlockFrozenLatchCanonicalBellman
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring C radius root)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (hbound : GrantBlockFrozenColdLeaseBound
      (ceilLogTwo n) S)
    (hfalse : S.success = false)
    (hmode :
      (S.fields (0 : Fin ((compileAdvice (ceilLogTwo n)).b + 1))).1 ≠
        .RESET) :
    n +
      (List.ofFn (fun edge : Fin n =>
        grantBlockFrozenColdLocalStoppedCredit n
          (ceilLogTwo n)
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root S edge))).sum ≤
    n * grantBlockFrozenColdLocalActiveCredit
      n (ceilLogTwo n) S := by
  have hlarge := Counter.resetColdLargeAtSpatialCutoff n hsp
  have hfields := grantBlockFrozenColdEmbedFields
    ring C root hbuffered.1 S hbound
  have hm := congrArg
    (fun p : Mode × Bool × BTok × Nat => p.1)
    (hfields 0 (by omega))
  change
    ((grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1 S).val root).mode =
      (S.fields (0 : Fin ((compileAdvice (ceilLogTwo n)).b + 1))).1
      at hm
  have hphysicalMode :
      ((grantBlockFrozenColdEmbedCarrier ring C root
        hbuffered.1 S).val root).mode ≠ .RESET := by
    intro hr
    exact hmode (hm.symm.trans hr)
  have hno : ∀ edge : Fin n,
      ¬ Counter.ResetClockBankDefectEntry ring
        (grantBlockFrozenColdEmbedCarrier ring C root
          hbuffered.1 S).val root edge := by
    intro edge
    exact (grantBlockFrozenColdEmbedOneStepFields
      ring C root radius hsp hbuffered S hbound hfalse edge).1
  have hrows := grantBlockFrozenLatchCanonicalRows
    ring C root radius hsp hbuffered S hbound hfalse
  exact grantBlockFrozenColdLocalBellmanOfCoveredRows
    ring root hsp hlarge
    (grantBlockFrozenColdEmbedCarrier ring C root
      hbuffered.1 S)
    S hfields hfalse hphysicalMode hno hrows

end L3

#print axioms L3.grantBlockFrozenLatchEmbedNoRequests
#print axioms L3.grantBlockFrozenLatchEmbedNoLeaders
#print axioms L3.grantBlockFrozenLatchTransitionGrant
#print axioms L3.grantBlockFrozenLatchCanonicalRootGrant
#print axioms L3.grantBlockFrozenLatchCanonicalEvent
#print axioms L3.grantBlockFrozenLatchCanonicalRows
#print axioms L3.grantBlockFrozenLatchCanonicalBellman
