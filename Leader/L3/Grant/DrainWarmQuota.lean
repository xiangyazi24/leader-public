import Leader.L3.Grant.DrainCompose

/-!
# Exact warm/ledger host synchronization for collective grant drain

No theorem in this file assumes
an unproved eight-n hit quota or the collective GrantFree cost.

The source model is the literal grantDrainStep.  The warm certificate
comes from the GrantDrainWarm module; its physical
state is synchronized with the already proved full-label source
ledger from GrantDrainEntrance.  No protocol state is modified.
-/

namespace L3.GrantDrainEntrance

open L3
open L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-- The two exact OLD-token Y-owner encodings coincide whenever the
OLD responder owns a physical grant.  This is finite local token
arithmetic; no claim of stochastic independence is made. -/
private theorem grantDrainWarmQuotaResponderRow
    {A : Type} (x y : A)
    (rx gx ry lx ly fresh : Bool) (fire : GrantDrainFire) :
    (if fire = .rightLocal ∨ fire = .cross ∨
        lx = true ∨ ly = true then (none : Option A)
     else if ry then some y
     else if (grantDrainTokenRow
       rx gx ry true lx ly fresh fire).1.grant then some x
     else none) =
    (match grantDrainLedgerYSource ry true lx ly fire
      (grantDrainTokenRow rx gx ry true lx ly fresh fire) with
     | some true => some y
     | some false => some x
     | none => none) := by
  cases rx <;> cases gx <;> cases ry <;>
    cases lx <;> cases ly <;> cases fresh <;>
    cases fire <;> rfl

/-- Local host update equality, including a coalescing Y-to-X
service.  Old occupancy is indispensable for the X-origin case:
a NEW X grant alone cannot authenticate an OLD X identity. -/
private theorem grantDrainWarmQuotaLocalTokenHost
    {n : Nat} (x y g : Fin n)
    (rx gx ry gy lx ly fresh : Bool) (fire : GrantDrainFire)
    (hX : g = x → gx = true)
    (hY : g = y → gy = true) :
    (if g = x then
       if (grantDrainTokenRow rx gx ry gy lx ly fresh fire).1.grant
       then some x else none
     else if g = y then
       if fire = .rightLocal ∨ fire = .cross ∨
           lx = true ∨ ly = true then none
       else if ry && gy then some y
       else if (grantDrainTokenRow
         rx gx ry gy lx ly fresh fire).1.grant then some x
       else none
     else some g) =
    (if g = x then
       if gx && (grantDrainTokenRow
         rx gx ry gy lx ly fresh fire).1.grant
       then some x else none
     else if g = y then
       match grantDrainLedgerYSource ry gy lx ly fire
         (grantDrainTokenRow rx gx ry gy lx ly fresh fire) with
       | some true => some y
       | some false => some x
       | none => none
     else some g) := by
  by_cases hgX : g = x
  · have hGX : gx = true := hX hgX
    simp [hgX, hGX]
  · by_cases hgY : g = y
    · have hGY : gy = true := hY hgY
      have hRow :=
        grantDrainWarmQuotaResponderRow x y
          rx gx ry lx ly fresh fire
      have hyx : ¬ y = x := fun h => hgX (hgY.trans h)
      simpa [hgX, hgY, hGY, hyx] using hRow
    · simp [hgX, hgY]

/-- The original warm ghost's host component, factored without
altering the full warm-label dynamics. -/
private def grantDrainWarmQuotaHostSelector
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (host : Option (Fin n)) : Option (Fin n) :=
  match host with
  | none => none
  | some g =>
      if g = e then
        if (grantDrainLedgerRow ring fresh s e).1.grant
        then some e else none
      else if g = ring.rightNeighbor e then
        if grantDrainSelect ring s e = .rightLocal ∨
            grantDrainSelect ring s e = .cross ∨
            (grantDrainNativeNext ring s e e).l = true ∨
            (grantDrainNativeNext ring s e
              (ring.rightNeighbor e)).l = true then none
        else if s.request (ring.rightNeighbor e) &&
            s.grant (ring.rightNeighbor e) then
          some (ring.rightNeighbor e)
        else if (grantDrainLedgerRow ring fresh s e).1.grant
          then some e
        else none
      else some g

/-- The nontrivial physical host bridge, not a relation between
arbitrary ungrounded proof-only labels. -/
theorem grantDrainWarmQuotaHostSelectorEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (host : Option (Fin n))
    (hPhysical : ∀ g : Fin n, host = some g →
      s.grant g = true) :
    grantDrainWarmQuotaHostSelector ring fresh s e host =
      grantDrainLedgerHost ring fresh s e host := by
  cases hh : host with
  | none =>
      rfl
  | some g =>
      have hX : g = e → s.grant e = true := by
        intro he
        rw [← he]
        exact hPhysical g hh
      have hY :
          g = ring.rightNeighbor e →
            s.grant (ring.rightNeighbor e) = true := by
        intro he
        rw [← he]
        exact hPhysical g hh
      have hRow :=
        grantDrainWarmQuotaLocalTokenHost
          e (ring.rightNeighbor e) g
          (s.request e) (s.grant e)
          (s.request (ring.rightNeighbor e))
          (s.grant (ring.rightNeighbor e))
          (grantDrainNativeNext ring s e e).l
          (grantDrainNativeNext ring s e
            (ring.rightNeighbor e)).l
          (fresh s e) (grantDrainSelect ring s e)
          hX hY
      exact hRow

/-- One real canonical transition updates the warm ghost and the
persistent marked ledger to the SAME host, provided their OLD hosts
agree and that host owns an OLD grant. -/
theorem grantDrainWarmQuotaHostStep
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (warm : GrantDrainWarmLabel n)
    (ledger : GrantDrainLedgerLabel n)
    (hHost : warm.host = ledger.host)
    (hPhysical : ∀ g : Fin n, warm.host = some g →
      s.grant g = true) :
    (grantDrainWarmLabelStep ring fresh update
      s e warm).host =
    (grantDrainLedgerStep ring fresh update
      s e ledger).host := by
  calc
    (grantDrainWarmLabelStep ring fresh update s e warm).host =
        grantDrainWarmQuotaHostSelector
          ring fresh s e warm.host := by rfl
    _ = grantDrainLedgerHost ring fresh s e warm.host :=
      grantDrainWarmQuotaHostSelectorEq
        ring fresh s e warm.host hPhysical
    _ = grantDrainLedgerHost ring fresh s e ledger.host := by
      rw [hHost]
    _ = (grantDrainLedgerStep ring fresh update
          s e ledger).host := by rfl

/-- The certified moving label and the already existing
full-source ledger on exactly one physical state.  Host equality is
needed only while the warm phase is active; a cold label cannot be
silently identified with a retired grant. -/
structure GrantDrainWarmQuotaJoint
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) where
  warm : GrantDrainWarmCertified (Scratch := Scratch) ring
  entrance : GrantDrainEntranceState n Scratch
  physicalEq : warm.state = entrance.physical
  hostEq : warm.label.warm = true →
    warm.label.host =
      (entrance.grantLabels warm.label.identity).host

/-- A clean-family cut with a genuinely warm physical grant provides
the synchronized initial ledger identity. -/
noncomputable def grantDrainWarmQuotaInitial
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    GrantDrainWarmQuotaJoint (Scratch := Scratch) ring := by
  refine
    { warm := grantDrainWarmCertifiedEntrance
        ring hn s g hC hWarm hGrant
      entrance := grantDrainEntranceInitial ring s
      physicalEq := rfl
      hostEq := ?_ }
  intro _
  change some g = (grantDrainLedgerInitial ring s g).host
  simp [grantDrainLedgerInitial, hGrant]

/-- The product uses one real scheduler edge; the certificate
and source marked ledger share the physical step exactly. -/
noncomputable def grantDrainWarmQuotaNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmQuotaJoint (Scratch := Scratch) ring)
    (e : Fin n) :
    GrantDrainWarmQuotaJoint (Scratch := Scratch) ring := by
  refine
    { warm := grantDrainWarmCertifiedNext
        ring hn fresh update z.warm e
      entrance := grantDrainEntranceNext
        ring fresh update z.entrance e
      physicalEq := ?_
      hostEq := ?_ }
  · change
        grantDrainStep ring fresh update z.warm.state e =
        grantDrainStep ring fresh update z.entrance.physical e
    exact congrArg
      (fun s => grantDrainStep ring fresh update s e)
      z.physicalEq
  · intro hNew
    change
      (grantDrainWarmLabelStep ring fresh update
        z.warm.state e z.warm.label).warm = true at hNew
    have hOld : z.warm.label.warm = true :=
      grantDrainD6HostNextWarmOld
        ring fresh update z.warm.state e z.warm.label hNew
    have hOldHost := z.hostEq hOld
    have hReal :
        ∀ g : Fin n, z.warm.label.host = some g →
          z.warm.state.grant g = true := by
      intro g hg
      exact z.warm.coherent g hOld hg
    have hStep :=
      grantDrainWarmQuotaHostStep
        ring fresh update z.warm.state e
        z.warm.label
        (z.entrance.grantLabels z.warm.label.identity)
        hOldHost hReal
    change
      (grantDrainWarmLabelStep ring fresh update
        z.warm.state e z.warm.label).host =
      (grantDrainLedgerStep ring fresh update
        z.entrance.physical e
        (z.entrance.grantLabels
          z.warm.label.identity)).host
    rw [← z.physicalEq]
    exact hStep

/-- A simultaneous scheduler word, with no second independent
schedule for the marked quota. -/
noncomputable def grantDrainWarmQuotaRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmQuotaJoint (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    GrantDrainWarmQuotaJoint (Scratch := Scratch) ring :=
  word.foldl (grantDrainWarmQuotaNext ring hn fresh update) z

/-- The marked-ledger projection is the already proved source
entrance ledger on the SAME complete scheduler word. -/
theorem grantDrainWarmQuotaRunEntrance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmQuotaJoint (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    (grantDrainWarmQuotaRun ring hn fresh update z word).entrance =
      grantDrainEntranceRun ring fresh update z.entrance word := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (grantDrainWarmQuotaRun ring hn fresh update
          (grantDrainWarmQuotaNext ring hn fresh update z e)
          rest).entrance =
        grantDrainEntranceRun ring fresh update
          (grantDrainEntranceNext ring fresh update z.entrance e) rest
      exact ih (grantDrainWarmQuotaNext ring hn fresh update z e)

/-- Warm-label identity cannot be changed by a native interaction,
canonical birth, grant coalescence, or leader sink. -/
theorem grantDrainWarmQuotaRunIdentity
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmQuotaJoint (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    (grantDrainWarmQuotaRun ring hn fresh update
      z word).warm.label.identity = z.warm.label.identity := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (grantDrainWarmQuotaRun ring hn fresh update
          (grantDrainWarmQuotaNext ring hn fresh update z e)
          rest).warm.label.identity = z.warm.label.identity
      calc
        _ = (grantDrainWarmQuotaNext
              ring hn fresh update z e).warm.label.identity :=
          ih (grantDrainWarmQuotaNext ring hn fresh update z e)
        _ = z.warm.label.identity := by rfl

/-- The requested THREE-way origin identification while the
tracked original label remains warm: the warm host = marked
source ledger host = faithful full-label ancestry host, at EVERY
scheduler prefix.  This is not an assumed leaf. -/
theorem grantDrainWarmQuotaLiveFullHostEq
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true)
    (word : List (Fin n))
    (hLive :
      (grantDrainWarmQuotaRun ring hn fresh update
        (grantDrainWarmQuotaInitial
          ring hn s g hC hWarm hGrant) word).warm.label.warm = true) :
    (grantDrainWarmQuotaRun ring hn fresh update
      (grantDrainWarmQuotaInitial
        ring hn s g hC hWarm hGrant) word).warm.label.host =
    (sharedGrantFaithfulGhost ring hn fresh update s).grantHost
      g word.reverse := by
  have hLocal :=
    (grantDrainWarmQuotaRun ring hn fresh update
      (grantDrainWarmQuotaInitial
        ring hn s g hC hWarm hGrant) word).hostEq hLive
  have hRun :=
    grantDrainWarmQuotaRunEntrance ring hn fresh update
      (grantDrainWarmQuotaInitial
        ring hn s g hC hWarm hGrant) word
  have hIdentity :=
    grantDrainWarmQuotaRunIdentity ring hn fresh update
      (grantDrainWarmQuotaInitial
        ring hn s g hC hWarm hGrant) word
  rw [hRun, hIdentity] at hLocal
  change
    (grantDrainWarmQuotaRun ring hn fresh update
      (grantDrainWarmQuotaInitial
        ring hn s g hC hWarm hGrant) word).warm.label.host =
    ((grantDrainEntranceRun ring fresh update
      (grantDrainEntranceInitial ring s) word).grantLabels g).host
      at hLocal
  exact hLocal.trans
    (sharedGrantFaithfulMarkFullHostEq
      ring hn fresh update s word g).symm

/-- Physical synchrony follows from the joint certificate on any
word, and preserves the exact original canonical source. -/
theorem grantDrainWarmQuotaRunPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainWarmQuotaJoint (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    (grantDrainWarmQuotaRun ring hn fresh update
      z word).warm.state =
    word.foldl (grantDrainStep ring fresh update) z.warm.state := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (grantDrainWarmQuotaRun ring hn fresh update
          (grantDrainWarmQuotaNext ring hn fresh update z e)
          rest).warm.state =
        rest.foldl (grantDrainStep ring fresh update)
          (grantDrainStep ring fresh update z.warm.state e)
      exact ih (grantDrainWarmQuotaNext ring hn fresh update z e)

/-- The ledger's syntactic marked quota is at most two n. -/
theorem grantDrainWarmQuotaLedgerCap
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (i : Fin n) :
    (grantDrainLedgerInitial ring s i).remaining ≤ 2 * n := by
  cases hg : s.grant i with
  | false =>
      simp [grantDrainLedgerInitial, hg]
  | true =>
      simp only [grantDrainLedgerInitial, hg, ↓reduceIte]
      exact grantDrainLedgerQuotaCap_le_double n _ _

/-- Numeric certificate for the two DIFFERENT phases.  It is not
a pathwise theorem that warmth ending starts a marked quota. -/
theorem grantDrainWarmQuotaCombinedCredits
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (g : Fin n)
    (hC : C_native ring s.native)
    (hWarm : grantDrainWarmAt s g = true)
    (hGrant : s.grant g = true) :
    grantDrainWarmCertifiedRank ring
      (grantDrainWarmCertifiedEntrance
        ring hn s g hC hWarm hGrant) +
      (grantDrainLedgerInitial ring s g).remaining ≤ 8 * n := by
  have hWarmCap :=
    grantDrainWarmCertifiedEntranceRankCap
      ring hn s g hC hWarm hGrant
  have hLockCap := grantDrainWarmQuotaLedgerCap ring s g
  omega

/-- Arithmetic for a genuine future 6n/2n handoff. -/
theorem grantDrainWarmQuotaHitBudget
    (n warmHits lockedHits : Nat)
    (hWarm : warmHits ≤ 6 * n)
    (hLocked : lockedHits ≤ 2 * n) :
    warmHits + lockedHits ≤ 8 * n := by
  omega

/-- Opaque polynomial arithmetic: does not normalize any scheduler
power or protocol-dependent symbolic exponent. -/
private theorem grantDrainWarmQuotaTwentyThreeOpaque (q : Nat) :
    3 * (23 * q) ≤ 82 * q := by
  omega

/-- The desired warmCap = 23n² fits the earlier arithmetic
interface.  No collective stochastic cost is inferred here. -/
theorem grantDrainWarmQuotaTwentyThreeFits (n : Nat) :
    3 * (23 * n ^ 2) ≤ 82 * n ^ 2 :=
  grantDrainWarmQuotaTwentyThreeOpaque (n ^ 2)

/-- The old loose paper warm cap of 29n² exceeds the
allocation by 5n² after tripling. -/
private theorem grantDrainWarmQuotaPaperGapOpaque (q : Nat) :
    3 * (29 * q) = 82 * q + 5 * q := by
  omega

theorem grantDrainWarmQuotaPaperGap (n : Nat) :
    3 * (29 * n ^ 2) = 82 * n ^ 2 + 5 * n ^ 2 :=
  grantDrainWarmQuotaPaperGapOpaque (n ^ 2)

/-- The 39n² fallback is below the paper's 40n² outer threshold
as a number, but has NOT been proved as a physical cost. -/
private theorem grantDrainWarmQuotaFallbackOpaque
    (q : Nat) (hq : 0 < q) :
    39 * q < 40 * q := by
  omega

theorem grantDrainWarmQuotaFallbackBelowForty
    (n : Nat) (hn : 5 ≤ n) :
    39 * n ^ 2 < 40 * n ^ 2 := by
  have hSq : 0 < n ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_pos (by omega) (by omega)
  exact grantDrainWarmQuotaFallbackOpaque (n ^ 2) hSq

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaHostSelectorEq
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaHostStep
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaRunEntrance
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaRunIdentity
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaLiveFullHostEq
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaRunPhysical
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaLedgerCap
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaCombinedCredits
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaHitBudget
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaTwentyThreeFits
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaPaperGap
#print axioms L3.GrantDrainEntrance.grantDrainWarmQuotaFallbackBelowForty
