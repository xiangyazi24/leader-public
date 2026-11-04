import Leader.L3.RenewalPreparationStage

/-!
BANK inherited-extinction no-new-producer identity and
the literal two-site token-owner fidelity.

No declaration in this file
assumes a grant-drain clock or a global warm-rank monotonicity theorem.
The source protocol and every existing module are unchanged.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! The native arguments of the token owner are the final, post-FIRE
native records. This statement does not assume that FIRE is absent. -/

private def nativeOutX {c : Compiled} (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).1

/-- The same for the responder site. -/
private def nativeOutY {c : Compiled} (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).2

private theorem agent_l_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).l = if p then a.l else b.l := by
  split <;> rfl

private theorem agent_b_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).b = if p then a.b else b.b := by
  split <;> rfl

private theorem agent_sh_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sh = if p then a.sh else b.sh := by
  split <;> rfl

private theorem agent_sg_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sg = if p then a.sg else b.sg := by
  split <;> rfl

private theorem baseStep_fst_l (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.l = (nativeOutX x y).l := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_l_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_l_ite]

private theorem baseStep_fst_b (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.b = (nativeOutX x y).b := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_b_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_b_ite]

private theorem baseStep_fst_sh (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.sh = (nativeOutX x y).sh := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]

private theorem baseStep_fst_sg (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.sg = (nativeOutX x y).sg := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]

private theorem baseStep_snd_l (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.l = (nativeOutY x y).l := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_l_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_l_ite]

private theorem baseStep_snd_b (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.b = (nativeOutY x y).b := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_b_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_b_ite]

private theorem baseStep_snd_sh (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.sh = (nativeOutY x y).sh := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]

private theorem baseStep_snd_sg (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.sg = (nativeOutY x y).sg := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]

/-- Structural native independence of certificate, PACK, BANK/SMALL,
    DCC, candidate, and token updates in baseStep. -/
private theorem baseStep_fst_native (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.certNative = nativeOutX x y := by
  have hl := baseStep_fst_l c ev x y
  have hb := baseStep_fst_b c ev x y
  have hsh := baseStep_fst_sh c ev x y
  have hsg := baseStep_fst_sg c ev x y
  show CertNative.mk (baseStep c ev x y).1.l (baseStep c ev x y).1.b
      (baseStep c ev x y).1.sh (baseStep c ev x y).1.sg = _
  rw [hl, hb, hsh, hsg]

private theorem baseStep_snd_native (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.certNative = nativeOutY x y := by
  have hl := baseStep_snd_l c ev x y
  have hb := baseStep_snd_b c ev x y
  have hsh := baseStep_snd_sh c ev x y
  have hsg := baseStep_snd_sg c ev x y
  show CertNative.mk (baseStep c ev x y).2.l (baseStep c ev x y).2.b
      (baseStep c ev x y).2.sh (baseStep c ev x y).2.sg = _
  rw [hl, hb, hsh, hsg]

/-- Post-FIRE native records are independent of non-native writers.
The baseStep helpers above project one field at a time. -/
private theorem bankStageFinalNativePair (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.certNative =
      (if fireAtSite
          (fireSelect x y
            (postEInfo x y).eX (postEInfo x y).eY)
          .siteX then firedNative else (postEInfo x y).eX) ∧
    (transition c x y).2.certNative =
      (if fireAtSite
          (fireSelect x y
            (postEInfo x y).eX (postEInfo x y).eY)
          .siteY then firedNative else (postEInfo x y).eY) := by
  have hx :
      (transition c x y).1.certNative =
        (baseStep c (certificateStep c x y).2.2 x y).1.certNative := rfl
  have hy :
      (transition c x y).2.certNative =
        (baseStep c (certificateStep c x y).2.2 x y).2.certNative := rfl
  constructor
  · rw [hx]
    exact baseStep_fst_native c (certificateStep c x y).2.2 x y
  · rw [hy]
    exact baseStep_snd_native c (certificateStep c x y).2.2 x y

/-! If the OLD BANK guard is false, the literal physical token owner
has precisely the inputs and outputs of renewalNoNewGrantTokens.
All OLD requests/grants and the FIRE result are unrestricted. -/

private theorem bankStageNoSuccessTokenEquality
    (c : Compiled) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hzero : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = false) :
    renewalNoNewGrantTokens c x y =
      baseTokenOutputs c (certificateStep c x y).2.2 x y := by
  have hn := bankStageFinalNativePair c x y
  have hbit : baseBankSuccessBit c x y = false := by
    simp [baseBankSuccessBit, hbank, hzero]
  unfold renewalNoNewGrantTokens baseTokenOutputs
  rw [hn.1, hn.2]
  simp only [hbit]
  rfl

private theorem bankStageMaskOffEqualsOnOfNoSuccess
    (c : Compiled) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hzero : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = false) :
    renewalMaskedPair c false x y =
      renewalMaskedPair c true x y := by
  have ht := bankStageNoSuccessTokenEquality c x y hbank hzero
  have hf := headlineRendezvousTransitionTokenFrame c x y
  have hxr :
      (transition c x y).1.req =
        (renewalNoNewGrantTokens c x y).1.req :=
    hf.1.trans
      (congrArg (fun t : TokPair × TokPair × TokMeta => t.1.req)
        ht.symm)
  have hxg :
      (transition c x y).1.grant =
        (renewalNoNewGrantTokens c x y).1.grant :=
    hf.2.1.trans
      (congrArg (fun t : TokPair × TokPair × TokMeta => t.1.grant)
        ht.symm)
  have hyr :
      (transition c x y).2.req =
        (renewalNoNewGrantTokens c x y).2.1.req :=
    hf.2.2.1.trans
      (congrArg (fun t : TokPair × TokPair × TokMeta => t.2.1.req)
        ht.symm)
  have hyg :
      (transition c x y).2.grant =
        (renewalNoNewGrantTokens c x y).2.1.grant :=
    hf.2.2.2.trans
      (congrArg (fun t : TokPair × TokPair × TokMeta => t.2.1.grant)
        ht.symm)
  change transition c x y =
    ({ (transition c x y).1 with
        req := (renewalNoNewGrantTokens c x y).1.req
        grant := (renewalNoNewGrantTokens c x y).1.grant },
     { (transition c x y).2 with
        req := (renewalNoNewGrantTokens c x y).2.1.req
        grant := (renewalNoNewGrantTokens c x y).2.1.grant })
  rw [← hxr, ← hxg, ← hyr, ← hyg]

/-- L20: inherited authority is no longer an effectful payer.
A true OLD success therefore activates the actual fresh mask.
With a false OLD success, the no-producer token row agrees with the
unmasked physical token row, including arbitrary OLD grants/FIRE. -/
theorem bankExtinctPairEqualsNoProducer {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (e : Fin n) :
    renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) =
      renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) := by
  cases hs : bankSuccess
      (bankCell (z.val.1 e) (z.val.1 e).pack.val)
      (bankCell (z.val.1 (ring.rightNeighbor e))
        (z.val.1 (ring.rightNeighbor e)).pack.val)
      (packNext (z.val.1 e).pack.val
        (z.val.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b with
  | true =>
      have hfresh :=
        (inheritedAuthorityExtinctNow ring hbank z hauth) e hs
      have hcut : renewalBankCut ring z.val.1 z.val.2 e = true := by
        simp [renewalBankCut, hs, hfresh]
      rw [hcut]
  | false =>
      have hcut : renewalBankCut ring z.val.1 z.val.2 e = false := by
        simp [renewalBankCut, hs]
      rw [hcut]
      exact bankStageMaskOffEqualsOnOfNoSuccess
        (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) hbank hs

/-! A separate literal fidelity leaf for L21.
Unlike a full simulation, this equality concerns only the two token
records. It does not conflate the masked reference successor with the
unmasked grantDrainRealScratchNext. -/

private def bankStageDrainFireToBase : GrantDrainFire → Option FireSel
  | .none => none
  | .leftLocal =>
      some {
        kind := .F0
        site := .siteX
        reqX := true
        grantX := true
      }
  | .rightLocal =>
      some {
        kind := .F1
        site := .siteY
        reqY := true
        grantY := true
      }
  | .cross =>
      some {
        kind := .F2
        site := .siteX
        reqX := true
        grantY := true
      }

private theorem bankStageLiteralTokenDrainRow {c : Compiled}
    (x y : Agent c) (fX fY : CertNative)
    (fresh : Bool) (fire : GrantDrainFire) :
    ((tokenStep x y fX fY
        (bankStageDrainFireToBase fire) fresh false).1,
     (tokenStep x y fX fY
        (bankStageDrainFireToBase fire) fresh false).2.1) =
      grantDrainTokenRow
        x.req x.grant y.req y.grant
        fX.l fY.l fresh fire := by
  cases hrx : x.req <;>
    cases hgx : x.grant <;>
    cases hry : y.req <;>
    cases hgy : y.grant <;>
    cases hlx : fX.l <;>
    cases hly : fY.l <;>
    cases fresh <;>
    cases fire <;>
    simp [bankStageDrainFireToBase, tokenStep,
      grantDrainTokenRow, fireAtSite,
      hrx, hgx, hry, hgy, hlx, hly] <;> decide

/-- The masked reference's TWO token outputs equal the no-producer
GrantDrain row when the FIRE classifier is the actual one.
This is deliberately not a claim of whole-Agent or scratch equality. -/
theorem bankNoProducerTokenOwnerFidelity
    (c : Compiled) (x y : Agent c) (fire : GrantDrainFire)
    (hfire :
      fireSelect x y (postEInfo x y).eX (postEInfo x y).eY =
        bankStageDrainFireToBase fire) :
    ((renewalNoNewGrantTokens c x y).1,
     (renewalNoNewGrantTokens c x y).2.1) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        (transition c x y).1.l (transition c x y).2.l
        (dccStep x y (certificateStep c x y).2.2).request
        fire := by
  unfold renewalNoNewGrantTokens
  rw [hfire]
  exact bankStageLiteralTokenDrainRow x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request fire

/-- Read only the request/grant fields of two physical Agents. -/
def bankStagePairTokens {c : Compiled}
    (p : Agent c × Agent c) : TokPair × TokPair :=
  ({ req := p.1.req, grant := p.1.grant },
   { req := p.2.req, grant := p.2.grant })

/-- All four masked token fields, including HOLD and movement,
agree with the reference's no-new-grant Drain row. -/
theorem bankMaskedPairTokenOwnerFidelity
    (c : Compiled) (x y : Agent c) (fire : GrantDrainFire)
    (hfire :
      fireSelect x y (postEInfo x y).eX (postEInfo x y).eY =
        bankStageDrainFireToBase fire) :
    bankStagePairTokens (renewalMaskedPair c true x y) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        (transition c x y).1.l (transition c x y).2.l
        (dccStep x y (certificateStep c x y).2.2).request fire := by
  change
    ((renewalNoNewGrantTokens c x y).1,
     (renewalNoNewGrantTokens c x y).2.1) =
      grantDrainTokenRow x.req x.grant y.req y.grant
        (transition c x y).1.l (transition c x y).2.l
        (dccStep x y (certificateStep c x y).2.2).request fire
  exact bankNoProducerTokenOwnerFidelity c x y fire hfire

end L3.RenewalReferenceClock


/-!
The inherited-extinct BANK reference as an adapted
no-new-grant GrantDrainState. The scratch IS the stamped and masked
BANK reference state, never the unmasked protocol successor.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The same first-match F0/F1/F2 selector, now typed for the
GrantDrain row. Eligibility is evaluated on the OLD pair's post-E
native fields, before any FIRE birth. -/
private def bankStageDrainPairFire {c : Compiled}
    (x y : Agent c) (pX pY : CertNative) : GrantDrainFire :=
  if x.req && x.grant && (!pX.l && pX.b.val == 0) then .leftLocal
  else if y.req && y.grant && (!pY.l && pY.b.val == 0) then .rightLocal
  else if x.req && y.grant && (!pX.l && pX.b.val == 0) then .cross
  else .none

/-- Physical FIRE preserves priority and every consumption flag
when expressed using the bankStageDrainFireToBase. -/
private theorem bankStageDrainPairFireCorrect {c : Compiled}
    (x y : Agent c) (pX pY : CertNative) :
    bankStageDrainFireToBase (bankStageDrainPairFire x y pX pY) =
      fireSelect x y pX pY := by
  unfold bankStageDrainPairFire fireSelect
  dsimp only
  by_cases hx :
      (x.req && x.grant && (!pX.l && pX.b.val == 0)) = true
  · simp only [if_pos hx, bankStageDrainFireToBase]
  · simp only [if_neg hx]
    by_cases hy :
        (y.req && y.grant && (!pY.l && pY.b.val == 0)) = true
    · simp only [if_pos hy, bankStageDrainFireToBase]
    · simp only [if_neg hy]
      by_cases hc :
          (x.req && y.grant && (!pX.l && pX.b.val == 0)) = true
      · simp only [if_pos hc, bankStageDrainFireToBase]
      · simp only [if_neg hc, bankStageDrainFireToBase]

/-- Unlike the unmasked real projection, the scratch is the complete
valid BANK reference, including the ghost controller/worker memory.
The edge history is kept separately because it is not a field of z. -/
def bankStageDrainProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) :
    GrantDrainState n (BankReferenceState ring hbank) :=
  { native := nativeProjection z.val.1
    request := fun i => (z.val.1 i).req
    grant := fun i => (z.val.1 i).grant
    scratch := z
    history := history }

/-- DCC is read from the complete OLD reference scratch, after
revealing the selected edge. No approximation of its private state. -/
def bankStageDrainFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (e : Fin n) : Bool :=
  (dccStep (s.scratch.val.1 e)
    (s.scratch.val.1 (ring.rightNeighbor e))
    (certificateStep (compileAdvice (ceilLogTwo n))
      (s.scratch.val.1 e)
      (s.scratch.val.1 (ring.rightNeighbor e))).2.2).request

/-- The adapted scratch update is literally the masked valid
referenceNext, not grantDrainRealScratchNext. -/
def bankStageDrainScratchNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (e : Fin n) : BankReferenceState ring hbank :=
  (bankValidRootedReferenceData ring hbank).referenceNext s.scratch e

/-- At n>=2 the nativeE selected endpoints really are the two
postEInfo records, with source priority and a distinct responder. -/
private theorem bankStageDrainPostENativePair {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    (nativeE ring (nativeProjection C) e e) =
      (postEInfo (C e) (C (ring.rightNeighbor e))).eX ∧
    (nativeE ring (nativeProjection C) e
      (ring.rightNeighbor e)) =
      (postEInfo (C e) (C (ring.rightNeighbor e))).eY := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  constructor
  · simp [nativeE, nativeProjection, postEInfo]
  · simp [nativeE, nativeProjection, postEInfo, hne]

/-- L21 (1): the no-producer Drain selector makes exactly the
same FIRE choice on the selected OLD physical pair. -/
theorem bankStageDrainSelectPair {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) :
    grantDrainSelect ring
        (bankStageDrainProjection ring hbank z history) e =
      bankStageDrainPairFire
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eY := by
  have hp := bankStageDrainPostENativePair ring hn z.val.1 e
  change
    (if (z.val.1 e).req && (z.val.1 e).grant &&
      grantDrainEligible (nativeE ring (nativeProjection z.val.1) e) e
     then GrantDrainFire.leftLocal
     else if (z.val.1 (ring.rightNeighbor e)).req &&
       (z.val.1 (ring.rightNeighbor e)).grant &&
       grantDrainEligible (nativeE ring (nativeProjection z.val.1) e)
         (ring.rightNeighbor e)
     then GrantDrainFire.rightLocal
     else if (z.val.1 e).req &&
       (z.val.1 (ring.rightNeighbor e)).grant &&
       grantDrainEligible (nativeE ring (nativeProjection z.val.1) e) e
     then GrantDrainFire.cross
     else GrantDrainFire.none) =
      bankStageDrainPairFire
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eY
  simpa only [grantDrainEligible, bankStageDrainPairFire,
    hp.1, hp.2]

theorem bankStageDrainSelectPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) :
    bankStageDrainFireToBase
      (grantDrainSelect ring
        (bankStageDrainProjection ring hbank z history) e) =
      fireSelect
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eY := by
  rw [bankStageDrainSelectPair ring hn hbank z history e]
  exact bankStageDrainPairFireCorrect
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (postEInfo (z.val.1 e)
      (z.val.1 (ring.rightNeighbor e))).eX
    (postEInfo (z.val.1 e)
      (z.val.1 (ring.rightNeighbor e))).eY

/-- A selected pair's final native records are post-E except for
the one site overwritten by its literal FIRE birth. -/
private theorem bankStageFinalNativePairByFire (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.certNative =
      (match bankStageDrainPairFire x y
          (postEInfo x y).eX (postEInfo x y).eY with
       | .leftLocal => firedNative
       | .cross => firedNative
       | _ => (postEInfo x y).eX) ∧
    (transition c x y).2.certNative =
      (match bankStageDrainPairFire x y
          (postEInfo x y).eX (postEInfo x y).eY with
       | .rightLocal => firedNative
       | _ => (postEInfo x y).eY) := by
  have hn := bankStageFinalNativePair c x y
  have hf := bankStageDrainPairFireCorrect x y
    (postEInfo x y).eX (postEInfo x y).eY
  simp only [← hf] at hn
  cases hc : bankStageDrainPairFire x y
      (postEInfo x y).eX (postEInfo x y).eY <;>
    simpa [hc, bankStageDrainFireToBase, fireAtSite] using hn

/-- The source field of the no-producer native row. Only the
selected FIRE tag is reduced; the whole grantDrainSelect definition
is not expanded. -/
private theorem bankStageDrainNativeAtSource {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (fire : GrantDrainFire)
    (hne : e ≠ ring.rightNeighbor e)
    (hsel : grantDrainSelect ring s e = fire) :
    (grantDrainNativeNext ring s e) e =
      match fire with
      | .leftLocal => firedNative
      | .cross => firedNative
      | _ => (nativeE ring s.native e) e := by
  cases fire <;>
    simp [grantDrainNativeNext, hsel, canonicalBirth, hne]

/-- The responder is distinct, so only F1 overwrites its native
field. F0 and F2 overwrite the source instead. -/
private theorem bankStageDrainNativeAtResponder {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e : Fin n) (fire : GrantDrainFire)
    (hne : ring.rightNeighbor e ≠ e)
    (hsel : grantDrainSelect ring s e = fire) :
    (grantDrainNativeNext ring s e) (ring.rightNeighbor e) =
      match fire with
      | .rightLocal => firedNative
      | _ => (nativeE ring s.native e) (ring.rightNeighbor e) := by
  cases fire <;>
    simp [grantDrainNativeNext, hsel, canonicalBirth, hne]

/-- Neither native E nor canonical birth touches an unselected site.
OLD requests and grants are arbitrary here. -/
private theorem bankStageDrainNativeAway {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (e i : Fin n) (fire : GrantDrainFire)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e)
    (hsel : grantDrainSelect ring s e = fire) :
    (grantDrainNativeNext ring s e) i = s.native i := by
  cases fire <;>
    simp [grantDrainNativeNext, hsel, canonicalBirth,
      nativeE, he, hj]

theorem bankStageDrainNativeNextMatches {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) :
    grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e =
      nativeProjection
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e).val.1 := by
  have hsel := bankStageDrainSelectPair
    ring hn hbank z history e
  have hshape := bankStageFinalNativePairByFire
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hpost := bankStageDrainPostENativePair
    ring hn z.val.1 e
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hrev : e ≠ ring.rightNeighbor e := by
    intro h
    exact hne h.symm
  have hframe :
      nativeProjection
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e).val.1 =
      nativeProjection (headlinePhysicalNext ring z.val.1 e) :=
    renewalBankValidNativeFrame ring hbank z e
  have hsource :
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e) e =
      (transition (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative := by
    cases hcase : bankStageDrainPairFire
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eY with
    | none =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .none := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e) e =
            (nativeE ring
              (bankStageDrainProjection ring hbank z history).native e)
                e := by
          simp [grantDrainNativeNext, hs]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative =
              (postEInfo (z.val.1 e)
                (z.val.1 (ring.rightNeighbor e))).eX := by
          simpa only [hcase] using hshape.1
        exact hleft.trans (hpost.1.trans hright.symm)
    | leftLocal =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .leftLocal := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e) e =
              firedNative := by
          simp [grantDrainNativeNext, hs, canonicalBirth]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative =
              firedNative := by
          simpa only [hcase] using hshape.1
        exact hleft.trans hright.symm
    | rightLocal =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .rightLocal := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e) e =
            (nativeE ring
              (bankStageDrainProjection ring hbank z history).native e)
                e := by
          simp [grantDrainNativeNext, hs, canonicalBirth, hrev]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative =
              (postEInfo (z.val.1 e)
                (z.val.1 (ring.rightNeighbor e))).eX := by
          simpa only [hcase] using hshape.1
        exact hleft.trans (hpost.1.trans hright.symm)
    | cross =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .cross := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e) e =
              firedNative := by
          simp [grantDrainNativeNext, hs, canonicalBirth]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative =
              firedNative := by
          simpa only [hcase] using hshape.1
        exact hleft.trans hright.symm
  have htarget :
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e)
        (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative := by
    cases hcase : bankStageDrainPairFire
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eX
        (postEInfo (z.val.1 e)
          (z.val.1 (ring.rightNeighbor e))).eY with
    | none =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .none := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e)
                (ring.rightNeighbor e) =
            (nativeE ring
              (bankStageDrainProjection ring hbank z history).native e)
                (ring.rightNeighbor e) := by
          simp [grantDrainNativeNext, hs]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative =
              (postEInfo (z.val.1 e)
                (z.val.1 (ring.rightNeighbor e))).eY := by
          simpa only [hcase] using hshape.2
        exact hleft.trans (hpost.2.trans hright.symm)
    | leftLocal =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .leftLocal := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e)
                (ring.rightNeighbor e) =
            (nativeE ring
              (bankStageDrainProjection ring hbank z history).native e)
                (ring.rightNeighbor e) := by
          simp [grantDrainNativeNext, hs, canonicalBirth, hne]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative =
              (postEInfo (z.val.1 e)
                (z.val.1 (ring.rightNeighbor e))).eY := by
          simpa only [hcase] using hshape.2
        exact hleft.trans (hpost.2.trans hright.symm)
    | rightLocal =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .rightLocal := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e)
                (ring.rightNeighbor e) =
              firedNative := by
          simp [grantDrainNativeNext, hs, canonicalBirth]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative =
              firedNative := by
          simpa only [hcase] using hshape.2
        exact hleft.trans hright.symm
    | cross =>
        have hs :
            grantDrainSelect ring
              (bankStageDrainProjection ring hbank z history) e =
              .cross := by
          simpa only [hcase] using hsel
        have hleft :
            (grantDrainNativeNext ring
              (bankStageDrainProjection ring hbank z history) e)
                (ring.rightNeighbor e) =
            (nativeE ring
              (bankStageDrainProjection ring hbank z history).native e)
                (ring.rightNeighbor e) := by
          simp [grantDrainNativeNext, hs, canonicalBirth, hne]
        have hright :
            (transition (compileAdvice (ceilLogTwo n))
              (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative =
              (postEInfo (z.val.1 e)
                (z.val.1 (ring.rightNeighbor e))).eY := by
          simpa only [hcase] using hshape.2
        exact hleft.trans (hpost.2.trans hright.symm)
  funext i
  have hf := congrArg
    (fun N : Fin n → CertNative => N i) hframe
  by_cases he : i = e
  · subst i
    calc
      (grantDrainNativeNext ring
          (bankStageDrainProjection ring hbank z history) e) e =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.certNative :=
        hsource
      _ = nativeProjection
            (headlinePhysicalNext ring z.val.1 e) e :=
        (congrArg Agent.certNative
          (headlineRendezvousStepAtSource ring z.val.1 e)).symm
      _ = nativeProjection
            ((bankValidRootedReferenceData ring hbank).referenceNext
              z e).val.1 e :=
        (congrArg
          (fun N : Fin n → CertNative => N e) hframe).symm
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      calc
        (grantDrainNativeNext ring
            (bankStageDrainProjection ring hbank z history) e)
            (ring.rightNeighbor e) =
          (transition (compileAdvice (ceilLogTwo n))
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.certNative :=
          htarget
        _ = nativeProjection
              (headlinePhysicalNext ring z.val.1 e)
              (ring.rightNeighbor e) :=
          (congrArg Agent.certNative
            (headlineRendezvousStepAtResponder
              ring hn z.val.1 e)).symm
        _ = nativeProjection
              ((bankValidRootedReferenceData ring hbank).referenceNext
                z e).val.1 (ring.rightNeighbor e) :=
          (congrArg
            (fun N : Fin n → CertNative =>
              N (ring.rightNeighbor e)) hframe).symm
    · have hrow :
          (grantDrainNativeNext ring
            (bankStageDrainProjection ring hbank z history) e) i =
          (z.val.1 i).certNative :=
        bankStageDrainNativeAway ring
          (bankStageDrainProjection ring hbank z history) e i
          (bankStageDrainPairFire
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
            (postEInfo (z.val.1 e)
              (z.val.1 (ring.rightNeighbor e))).eX
            (postEInfo (z.val.1 e)
              (z.val.1 (ring.rightNeighbor e))).eY)
          he hj hsel
      calc
        (grantDrainNativeNext ring
            (bankStageDrainProjection ring hbank z history) e) i =
          (z.val.1 i).certNative := hrow
        _ = nativeProjection
              (headlinePhysicalNext ring z.val.1 e) i :=
          (congrArg Agent.certNative
            (headlineRendezvousStepAway
              ring z.val.1 e i he hj)).symm
        _ = nativeProjection
              ((bankValidRootedReferenceData ring hbank).referenceNext
                z e).val.1 i := hf.symm


/-- The two final leader bits entering the Drain token row are
the actual post-FIRE source and responder leader bits. -/
private theorem bankStageDrainFinalLeaders {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) :
    (grantDrainNativeNext ring
      (bankStageDrainProjection ring hbank z history) e e).l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l ∧
    (grantDrainNativeNext ring
      (bankStageDrainProjection ring hbank z history) e
      (ring.rightNeighbor e)).l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l := by
  have hnative :=
    bankStageDrainNativeNextMatches ring hn hbank z history e
  have hphysical :=
    renewalBankValidNativeFrame ring hbank z e
  constructor
  · have ha := congrArg
        (fun N : Fin n → CertNative => (N e).l) hnative
    have hb := congrArg
        (fun N : Fin n → CertNative => (N e).l) hphysical
    have hc := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.l)
        (headlineRendezvousStepAtSource ring z.val.1 e)
    exact ha.trans (hb.trans hc)
  · have ha := congrArg
        (fun N : Fin n → CertNative =>
          (N (ring.rightNeighbor e)).l) hnative
    have hb := congrArg
        (fun N : Fin n → CertNative =>
          (N (ring.rightNeighbor e)).l) hphysical
    have hc := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.l)
        (headlineRendezvousStepAtResponder ring hn z.val.1 e)
    exact ha.trans (hb.trans hc)

/-- The literal token row on the adapted projected state; the
extra scratch is used only by the DCC fresh-request decision. -/
private def bankStageDrainRow {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) : TokPair × TokPair :=
  grantDrainTokenRow
    (z.val.1 e).req (z.val.1 e).grant
    (z.val.1 (ring.rightNeighbor e)).req
    (z.val.1 (ring.rightNeighbor e)).grant
    (grantDrainNativeNext ring
      (bankStageDrainProjection ring hbank z history) e e).l
    (grantDrainNativeNext ring
      (bankStageDrainProjection ring hbank z history) e
        (ring.rightNeighbor e)).l
    (bankStageDrainFresh ring hbank
      (bankStageDrainProjection ring hbank z history) e)
    (grantDrainSelect ring
      (bankStageDrainProjection ring hbank z history) e)

/-- Under extinction the actual mask is a no-producer mask,
even with arbitrary OLD grants and a true physical BANK success. -/
private theorem bankStageDrainMaskedTokenPair {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n)) (e : Fin n) :
    bankStagePairTokens
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))) =
      bankStageDrainRow ring hbank z history e := by
  have hpair := bankExtinctPairEqualsNoProducer
    ring hbank z hauth e
  have hfire :=
    bankStageDrainSelectPhysical ring hn hbank z history e
  have htoken := bankMaskedPairTokenOwnerFidelity
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (grantDrainSelect ring
      (bankStageDrainProjection ring hbank z history) e)
    hfire.symm
  have hleaders :=
    bankStageDrainFinalLeaders ring hn hbank z history e
  change
    bankStagePairTokens
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))) =
      grantDrainTokenRow
        (z.val.1 e).req (z.val.1 e).grant
        (z.val.1 (ring.rightNeighbor e)).req
        (z.val.1 (ring.rightNeighbor e)).grant
        (grantDrainNativeNext ring
          (bankStageDrainProjection ring hbank z history) e e).l
        (grantDrainNativeNext ring
          (bankStageDrainProjection ring hbank z history) e
          (ring.rightNeighbor e)).l
        (dccStep (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
          (certificateStep (compileAdvice (ceilLogTwo n))
            (z.val.1 e)
            (z.val.1 (ring.rightNeighbor e))).2.2).request
        (grantDrainSelect ring
          (bankStageDrainProjection ring hbank z history) e)
  rw [hpair, hleaders.1, hleaders.2]
  exact htoken

/-- Extensionality for all five coordinates of the actual Drain
structure. Do not discard scratch or the adapted edge history. -/
private theorem bankStageDrainStateExt {n : Nat} {Scratch : Type}
    (s t : GrantDrainState n Scratch)
    (hn : s.native = t.native)
    (hr : s.request = t.request)
    (hg : s.grant = t.grant)
    (hs : s.scratch = t.scratch)
    (hh : s.history = t.history) : s = t := by
  cases s
  cases t
  cases hn
  cases hr
  cases hg
  cases hs
  cases hh
  rfl

/-- Req is a record field, and the masked step's two-level
source-priority update preserves the original selected-edge order. -/
private theorem bankStageMaskedRequestAt {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e i : Fin n) (suppress : Bool) :
    (renewalMaskedStep ring C e suppress i).req =
      if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
          (C e) (C (ring.rightNeighbor e))).1.req
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
          (C e) (C (ring.rightNeighbor e))).2.req
      else (C i).req := by
  by_cases h1 : i = e
  · rw [if_pos h1]
    exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.req)
      (show renewalMaskedStep ring C e suppress i = _ from if_pos h1)
  · by_cases h2 : i = ring.rightNeighbor e
    · rw [if_neg h1, if_pos h2]
      exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.req)
        (show renewalMaskedStep ring C e suppress i = _ from
          (if_neg h1).trans (if_pos h2))
    · rw [if_neg h1, if_neg h2]
      exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.req)
        (show renewalMaskedStep ring C e suppress i = _ from
          (if_neg h1).trans (if_neg h2))

/-- The same fieldwise frame for the OLD grant owner. -/
private theorem bankStageMaskedGrantAt {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e i : Fin n) (suppress : Bool) :
    (renewalMaskedStep ring C e suppress i).grant =
      if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
          (C e) (C (ring.rightNeighbor e))).1.grant
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
          (C e) (C (ring.rightNeighbor e))).2.grant
      else (C i).grant := by
  by_cases h1 : i = e
  · rw [if_pos h1]
    exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.grant)
      (show renewalMaskedStep ring C e suppress i = _ from if_pos h1)
  · by_cases h2 : i = ring.rightNeighbor e
    · rw [if_neg h1, if_pos h2]
      exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.grant)
        (show renewalMaskedStep ring C e suppress i = _ from
          (if_neg h1).trans (if_pos h2))
    · rw [if_neg h1, if_neg h2]
      exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.grant)
        (show renewalMaskedStep ring C e suppress i = _ from
          (if_neg h1).trans (if_neg h2))

/-- The actual Drain step writes precisely its two-site row; this
is a plain function-field projection rather than a claim of
whole-state definitional equality. -/
private theorem bankStageDrainStepRequestAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e i : Fin n) :
    (grantDrainStep ring
      (bankStageDrainFresh ring hbank)
      (bankStageDrainScratchNext ring hbank)
      (bankStageDrainProjection ring hbank z history) e).request i =
      if i = e then (bankStageDrainRow ring hbank z history e).1.req
      else if i = ring.rightNeighbor e then
        (bankStageDrainRow ring hbank z history e).2.req
      else (z.val.1 i).req := by
  rfl

private theorem bankStageDrainStepGrantAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e i : Fin n) :
    (grantDrainStep ring
      (bankStageDrainFresh ring hbank)
      (bankStageDrainScratchNext ring hbank)
      (bankStageDrainProjection ring hbank z history) e).grant i =
      if i = e then (bankStageDrainRow ring hbank z history e).1.grant
      else if i = ring.rightNeighbor e then
        (bankStageDrainRow ring hbank z history e).2.grant
      else (z.val.1 i).grant := by
  rfl

theorem bankStageDrainReferenceStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n)) (e : Fin n) :
    bankStageDrainProjection ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e)
      (e :: history) =
    grantDrainStep ring
      (bankStageDrainFresh ring hbank)
      (bankStageDrainScratchNext ring hbank)
      (bankStageDrainProjection ring hbank z history) e := by
  have ht :=
    bankStageDrainMaskedTokenPair ring hn hbank z hauth history e
  have hmask :
      ((bankValidRootedReferenceData ring hbank).referenceNext
        z e).val.1 =
      renewalMaskedStep ring z.val.1 e
        (renewalBankCut ring z.val.1 z.val.2 e) := rfl
  have hsourceReq :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.req =
      (bankStageDrainRow ring hbank z history e).1.req :=
    congrArg (fun p : TokPair × TokPair => p.1.req) ht
  have htargetReq :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.req =
      (bankStageDrainRow ring hbank z history e).2.req :=
    congrArg (fun p : TokPair × TokPair => p.2.req) ht
  have hsourceGrant :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.grant =
      (bankStageDrainRow ring hbank z history e).1.grant :=
    congrArg (fun p : TokPair × TokPair => p.1.grant) ht
  have htargetGrant :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.grant =
      (bankStageDrainRow ring hbank z history e).2.grant :=
    congrArg (fun p : TokPair × TokPair => p.2.grant) ht
  apply bankStageDrainStateExt
  · exact (bankStageDrainNativeNextMatches
      ring hn hbank z history e).symm
  · funext i
    have hp :=
      congrArg (fun C : HeadlineConfiguration n => (C i).req) hmask
    have hrow := bankStageMaskedRequestAt ring z.val.1 e i
      (renewalBankCut ring z.val.1 z.val.2 e)
    have hd := bankStageDrainStepRequestAt
      ring hbank z history e i
    calc
      (bankStageDrainProjection ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)
        (e :: history)).request i =
        (renewalMaskedStep ring z.val.1 e
          (renewalBankCut ring z.val.1 z.val.2 e) i).req := hp
      _ = (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.req
        else if i = ring.rightNeighbor e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring z.val.1 z.val.2 e)
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.req
        else (z.val.1 i).req) := hrow
      _ = (if i = e then
        (bankStageDrainRow ring hbank z history e).1.req
        else if i = ring.rightNeighbor e then
          (bankStageDrainRow ring hbank z history e).2.req
        else (z.val.1 i).req) := by
          split
          · exact hsourceReq
          · split
            · exact htargetReq
            · rfl
      _ = (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        (bankStageDrainProjection ring hbank z history) e).request i :=
          hd.symm
  · funext i
    have hp :=
      congrArg (fun C : HeadlineConfiguration n => (C i).grant) hmask
    have hrow := bankStageMaskedGrantAt ring z.val.1 e i
      (renewalBankCut ring z.val.1 z.val.2 e)
    have hd := bankStageDrainStepGrantAt
      ring hbank z history e i
    calc
      (bankStageDrainProjection ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)
        (e :: history)).grant i =
        (renewalMaskedStep ring z.val.1 e
          (renewalBankCut ring z.val.1 z.val.2 e) i).grant := hp
      _ = (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.grant
        else if i = ring.rightNeighbor e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring z.val.1 z.val.2 e)
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.grant
        else (z.val.1 i).grant) := hrow
      _ = (if i = e then
        (bankStageDrainRow ring hbank z history e).1.grant
        else if i = ring.rightNeighbor e then
          (bankStageDrainRow ring hbank z history e).2.grant
        else (z.val.1 i).grant) := by
          split
          · exact hsourceGrant
          · split
            · exact htargetGrant
            · rfl
      _ = (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        (bankStageDrainProjection ring hbank z history) e).grant i :=
          hd.symm
  · rfl
  · rfl


/-- The terminal predicates are the exact same predicate on
the projected native/physical grant-owner field. -/
theorem bankStageDrainGrantFreeIff {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) :
    NativeLiftGrantFree z.val.1 ↔
      GrantFree (bankStageDrainProjection ring hbank z history) := by
  rfl

/-- L21 (4): stronger than the requested cost comparison. There
is equality of every finite-horizon IID numerator, because the
same scheduler letters and the same first-hit predicate are used.
InheritedAuthorityExtinct is closed on the actual BANK reference. -/
theorem bankStageDrainCostNumeratorEq {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n)) (T : Nat) :
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T =
      costNumerator
        (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank))
        (fun s : GrantDrainState n
            (BankReferenceState ring hbank) => GrantFree s)
        (bankStageDrainProjection ring hbank z history) T := by
  classical
  have hcost :
      ∀ U (a : BankReferenceState ring hbank)
        (past : List (Fin n)),
        InheritedAuthorityExtinct ring hbank a →
        costNumerator
          (bankValidRootedReferenceData ring hbank).referenceNext
          (fun v => NativeLiftGrantFree v.val.1) a U =
        costNumerator
          (grantDrainStep ring
            (bankStageDrainFresh ring hbank)
            (bankStageDrainScratchNext ring hbank))
          (fun s : GrantDrainState n
              (BankReferenceState ring hbank) => GrantFree s)
          (bankStageDrainProjection ring hbank a past) U := by
    intro U
    induction U with
    | zero =>
        intro a past _
        simp only [costNumerator_zero]
    | succ U ih =>
        intro a past ha
        by_cases hstop : NativeLiftGrantFree a.val.1
        · have hd :
            GrantFree (bankStageDrainProjection ring hbank a past) :=
              (bankStageDrainGrantFreeIff ring hbank a past).mp hstop
          rw [costNumerator_terminal
              (bankValidRootedReferenceData ring hbank).referenceNext
              (fun v => NativeLiftGrantFree v.val.1) a hstop (U + 1),
              costNumerator_terminal
              (grantDrainStep ring
                (bankStageDrainFresh ring hbank)
                (bankStageDrainScratchNext ring hbank))
              (fun s : GrantDrainState n
                  (BankReferenceState ring hbank) => GrantFree s)
              (bankStageDrainProjection ring hbank a past)
              hd (U + 1)]
        · have hd :
            ¬ GrantFree (bankStageDrainProjection ring hbank a past) :=
              fun hh => hstop
                ((bankStageDrainGrantFreeIff ring hbank a past).mpr hh)
          rw [costNumerator_succ
              (bankValidRootedReferenceData ring hbank).referenceNext
              (fun v => NativeLiftGrantFree v.val.1) a hstop U,
              costNumerator_succ
              (grantDrainStep ring
                (bankStageDrainFresh ring hbank)
                (bankStageDrainScratchNext ring hbank))
              (fun s : GrantDrainState n
                  (BankReferenceState ring hbank) => GrantFree s)
              (bankStageDrainProjection ring hbank a past) hd U]
          have hedge (e : Fin n) :
              costNumerator
                  (bankValidRootedReferenceData ring hbank).referenceNext
                  (fun v => NativeLiftGrantFree v.val.1)
                  ((bankValidRootedReferenceData ring hbank).referenceNext
                    a e) U =
              costNumerator
                  (grantDrainStep ring
                    (bankStageDrainFresh ring hbank)
                    (bankStageDrainScratchNext ring hbank))
                  (fun s : GrantDrainState n
                      (BankReferenceState ring hbank) => GrantFree s)
                  (grantDrainStep ring
                    (bankStageDrainFresh ring hbank)
                    (bankStageDrainScratchNext ring hbank)
                    (bankStageDrainProjection ring hbank a past) e) U := by
            have hsquare :=
              bankStageDrainReferenceStep ring hn hbank a ha past e
            rw [← hsquare]
            exact ih
              ((bankValidRootedReferenceData ring hbank).referenceNext
                a e) (e :: past)
              (inheritedAuthorityExtinctStep ring hbank a ha e)
          exact congrArg (fun k : Nat => n ^ (U + 1) + k)
            (ofFn_sum_eq _ _ hedge)
  exact hcost T z history hauth

theorem bankStageDrainCostNumeratorLe {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n)) (T : Nat) :
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T ≤
      costNumerator
        (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank))
        (fun s : GrantDrainState n
            (BankReferenceState ring hbank) => GrantFree s)
        (bankStageDrainProjection ring hbank z history) T := by
  exact Nat.le_of_eq
    (bankStageDrainCostNumeratorEq ring hn hbank z hauth history T)

end L3.RenewalReferenceClock


/-!
No-new-grant ownership and the precise nominated-rank
obligation for the extinct-authority BANK reference.

A grant can MOVE into an empty site. The true no-producer invariant
is pairwise noncloning, not sitewise grant-bit monotonicity.
The quantitative theorem below explicitly requires a certified
global rank and its nominated edge, rather than postulating the
missing charged-label drift.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The literal false-producer row on the actual extinct BANK cut.
All OLD request and grant bits, and all possible FIRE cases, remain
unrestricted. This is L20 in a token-only form. -/
theorem bankExtinctNoNewGrantTokenOwner {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (e : Fin n) :
    bankStagePairTokens
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))) =
      ((renewalNoNewGrantTokens (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1,
       (renewalNoNewGrantTokens (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.1) := by
  rw [bankExtinctPairEqualsNoProducer ring hbank z hauth e]
  rfl

/-- The exact counterexample to a per-site no-new-grant assertion:
an OLD responder grant travels to a previously empty source. The
total grant count remains one, and the fresh producer bit is false. -/
theorem bankDrainOldGrantMayEnterEmptySource :
    (grantDrainTokenRow false false false true
      false false false GrantDrainFire.none).1.grant = true := by
  unfold grantDrainTokenRow
  decide

/-- L21 noncloning on the ACTUAL extinct BANK reference masked pair.
An OLD grant may move from Y to X, but fresh DCC requests and the
masked BANK success cannot increase the number of grant slots.
This is a two-site statement, not per-site monotonicity. -/
theorem bankExtinctMaskedGrantPairNoncloning {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n)) (e : Fin n) :
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) ≤
    (if (z.val.1 e).grant then 1 else 0) +
    (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  have hpair :=
    bankStageDrainMaskedTokenPair ring hn hbank z hauth history e
  have hrow :
      (if (bankStageDrainRow ring hbank z history e).1.grant
        then 1 else 0) +
      (if (bankStageDrainRow ring hbank z history e).2.grant
        then 1 else 0) ≤
      (if (z.val.1 e).grant then 1 else 0) +
      (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
    exact grantDrainTokenRow_noncloning
      (z.val.1 e).req (z.val.1 e).grant
      (z.val.1 (ring.rightNeighbor e)).req
      (z.val.1 (ring.rightNeighbor e)).grant
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e e).l
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e
        (ring.rightNeighbor e)).l
      (bankStageDrainFresh ring hbank
        (bankStageDrainProjection ring hbank z history) e)
      (grantDrainSelect ring
        (bankStageDrainProjection ring hbank z history) e)
  calc
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) =
      (if (bankStageDrainRow ring hbank z history e).1.grant
        then 1 else 0) +
      (if (bankStageDrainRow ring hbank z history e).2.grant
        then 1 else 0) := by
          exact congrArg
            (fun p : TokPair × TokPair =>
              (if p.1.grant then 1 else 0) +
              (if p.2.grant then 1 else 0)) hpair
    _ ≤ (if (z.val.1 e).grant then 1 else 0) +
        (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) :=
      hrow

/-- For the adapted projected drain, the SAME pairwise noncloning
holds on every edge. This does not need authority extinction, since
grantDrainStep has no fresh grant producer at all. -/
theorem bankProjectedDrainGrantPairNoncloning {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) (e : Fin n) :
    (if (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          (bankStageDrainProjection ring hbank z history) e).grant e
      then 1 else 0) +
    (if (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          (bankStageDrainProjection ring hbank z history) e).grant
          (ring.rightNeighbor e)
      then 1 else 0) ≤
    (if (z.val.1 e).grant then 1 else 0) +
    (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hs :
      (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        (bankStageDrainProjection ring hbank z history) e).grant e =
      (bankStageDrainRow ring hbank z history e).1.grant := by
    exact (bankStageDrainStepGrantAt ring hbank z history e e).trans
      (if_pos rfl)
  have ht :
      (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        (bankStageDrainProjection ring hbank z history) e).grant
        (ring.rightNeighbor e) =
      (bankStageDrainRow ring hbank z history e).2.grant := by
    exact (bankStageDrainStepGrantAt
        ring hbank z history e (ring.rightNeighbor e)).trans
      ((if_neg hne).trans (if_pos rfl))
  have hrow :
      (if (bankStageDrainRow ring hbank z history e).1.grant
        then 1 else 0) +
      (if (bankStageDrainRow ring hbank z history e).2.grant
        then 1 else 0) ≤
      (if (z.val.1 e).grant then 1 else 0) +
      (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
    exact grantDrainTokenRow_noncloning
      (z.val.1 e).req (z.val.1 e).grant
      (z.val.1 (ring.rightNeighbor e)).req
      (z.val.1 (ring.rightNeighbor e)).grant
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e e).l
      (grantDrainNativeNext ring
        (bankStageDrainProjection ring hbank z history) e
        (ring.rightNeighbor e)).l
      (bankStageDrainFresh ring hbank
        (bankStageDrainProjection ring hbank z history) e)
      (grantDrainSelect ring
        (bankStageDrainProjection ring hbank z history) e)
  calc
    (if (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          (bankStageDrainProjection ring hbank z history) e).grant e
      then 1 else 0) +
    (if (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          (bankStageDrainProjection ring hbank z history) e).grant
          (ring.rightNeighbor e)
      then 1 else 0) =
      (if (bankStageDrainRow ring hbank z history e).1.grant
        then 1 else 0) +
      (if (bankStageDrainRow ring hbank z history e).2.grant
        then 1 else 0) := by
          simp only [hs, ht]
    _ ≤ (if (z.val.1 e).grant then 1 else 0) +
        (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) :=
      hrow

/-- Exactly the three missing hypotheses required by the
grantDrain_cost_of_certified_nominated_rank theorem: a state-wide
rank with a nominated drop, all-edge nonincrease, and an initial
budget. No such rank is constructed here.

A single charged warm label is not a scalar global rank: it has
a host, warm status, remaining-birth credits and an exceptional
credit that must be propagated through every edge. -/
def BankExtinctGrantDrainRankCertificate {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) : Prop :=
  ∃ (rank : GrantDrainState n
        (BankReferenceState ring hbank) → Nat)
    (chosen : GrantDrainState n
        (BankReferenceState ring hbank) → Fin n),
    (∀ s : GrantDrainState n (BankReferenceState ring hbank),
      ¬ GrantFree s →
        rank (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          s (chosen s)) + 1 ≤ rank s) ∧
    (∀ s : GrantDrainState n (BankReferenceState ring hbank),
      ¬ GrantFree s → ∀ e : Fin n,
        rank (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          s e) ≤ rank s) ∧
    n * rank (bankStageDrainProjection ring hbank z history) ≤
      grantDrainCeiling n

/-- The sigma_G numerator bound, conditional on precisely the
nominated-rank certificate above. The projection is
unchanged; no positivity or drift fact is silently assumed. -/
theorem bankExtinctGrantDrainCeilingCost {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n))
    (hcertificate :
      BankExtinctGrantDrainRankCertificate ring hbank z history)
    (T : Nat) :
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T ≤
      n ^ T * grantDrainCeiling n := by
  obtain ⟨rank, chosen, hdrop, hnoninc, hbudget⟩ := hcertificate
  calc
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T ≤
      costNumerator
        (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank))
        (fun s : GrantDrainState n
            (BankReferenceState ring hbank) => GrantFree s)
        (bankStageDrainProjection ring hbank z history) T :=
      bankStageDrainCostNumeratorLe
        ring hn hbank z hauth history T
    _ ≤ n ^ T * grantDrainCeiling n :=
      grantDrain_cost_of_certified_nominated_rank ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        rank chosen hdrop hnoninc
        (bankStageDrainProjection ring hbank z history)
        hbudget T

end L3.RenewalReferenceClock


/-!
A restricted-domain nominated-edge cost theorem and the
precise protected BANK-reference rank certificate.

The paper's simultaneous grant-label tail proof does not provide
one bounded scalar rank with one strict nominated edge at every
live cut. The restricted nominated theorem is nevertheless useful
for any later scalar-potential approach. The rank hypothesis below
is kept explicit; no missing native or label-drift fact is assumed.
-/

namespace L3.Prob

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Bellman induction restricted to a class closed under every
nonterminal selected edge. No closure after hitting P is needed. -/
theorem costNumerator_le_of_potential_on
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P I : S → Prop)
    (Φ : S → Nat)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e : Fin n, I (next x e))
    (hdrift : ∀ x, I x → ¬ P x →
      n + (List.ofFn (fun e : Fin n => Φ (next x e))).sum ≤
        n * Φ x) :
    ∀ x, I x → ∀ T,
      costNumerator next P x T ≤ n ^ T * Φ x := by
  classical
  have hmain :
      ∀ T (x : S), I x →
        costNumerator next P x T ≤ n ^ T * Φ x := by
    intro T
    induction T with
    | zero =>
        intro x _
        simp only [costNumerator_zero]
        exact Nat.zero_le _
    | succ T ih =>
        intro x hx
        by_cases hp : P x
        · rw [costNumerator_terminal next P x hp (T + 1)]
          exact Nat.zero_le _
        · rw [costNumerator_succ next P x hp T]
          have hs := ofFn_sum_le
            (fun e : Fin n => costNumerator next P (next x e) T)
            (fun e : Fin n => n ^ T * Φ (next x e))
            (fun e => ih (next x e) (hclosed x hx hp e))
          calc
            n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator next P (next x e) T)).sum ≤
              n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  n ^ T * Φ (next x e))).sum :=
              Nat.add_le_add_left hs _
            _ = n ^ T *
                  (n + (List.ofFn (fun e : Fin n =>
                    Φ (next x e))).sum) := by
              rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
              all_goals ac_rfl
            _ ≤ n ^ T * (n * Φ x) :=
              Nat.mul_le_mul_left _ (hdrift x hx hp)
            _ = n ^ (T + 1) * Φ x := by
              rw [Nat.pow_succ]
              ac_rfl
  intro x hx T
  exact hmain T x hx

/-- A single nominated scheduler letter contributes one spike.
This is valid even at n=0, where Fin n has no inhabitants. -/
private theorem restrictedSumOneSpike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- The restricted-domain version of ProbStages'
costNumerator_le_of_nominated_edge. The nominated edge and
nonincrease are assumed only at nonterminal states in I, with
I closed on every nonterminal edge. Outside I the transition and
rank may behave arbitrarily. -/
theorem costNumerator_le_of_nominated_edge_on
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P I : S → Prop)
    (Φ : S → Nat) (chosen : S → Fin n)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e : Fin n, I (next x e))
    (hdrop : ∀ x, I x → ¬ P x →
      Φ (next x (chosen x)) + 1 ≤ Φ x)
    (hnoninc : ∀ x, I x → ¬ P x → ∀ e : Fin n,
      Φ (next x e) ≤ Φ x) :
    ∀ x, I x → ∀ T,
      costNumerator next P x T ≤ n ^ T * (n * Φ x) := by
  classical
  apply costNumerator_le_of_potential_on next P I
    (fun x => n * Φ x) hclosed
  intro x hx hp
  have hpoint : ∀ e : Fin n,
      Φ (next x e) + (if e = chosen x then 1 else 0) ≤ Φ x := by
    intro e
    by_cases he : e = chosen x
    · subst e
      simpa using hdrop x hx hp
    · simpa [he] using hnoninc x hx hp e
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      Φ (next x e) + (if e = chosen x then 1 else 0))
    (fun _ : Fin n => Φ x) hpoint
  rw [ofFn_sum_add, restrictedSumOneSpike n (chosen x) 1,
    ofFn_sum_const] at hsum
  calc
    n + (List.ofFn (fun e : Fin n => n * Φ (next x e))).sum =
        n * ((List.ofFn (fun e : Fin n => Φ (next x e))).sum + 1) := by
      rw [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ n * (n * Φ x) := Nat.mul_le_mul_left n hsum

end L3.Prob

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The closed protected portion of the projected, stamped BANK
reference. The existential explicitly binds the actual full
reference scratch and its genuine selected-edge history.
It is not the unrestricted Cartesian GrantDrainState. -/
def BankExtinctDrainProtectedDomain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) : Prop :=
  ∃ (z : BankReferenceState ring hbank)
    (history : List (Fin n)),
    headlineRooted ring z.val.1 ∧
    InheritedAuthorityExtinct ring hbank z ∧
    s = bankStageDrainProjection ring hbank z history

/-- The full protected/extinct projected class is forward closed.
The proof uses the true masked reference successor in scratch,
not the unmasked physical protocol step. -/
theorem bankExtinctDrainProtectedDomainClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (hs : BankExtinctDrainProtectedDomain ring hbank s)
    (e : Fin n) :
    BankExtinctDrainProtectedDomain ring hbank
      (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank) s e) := by
  obtain ⟨z, history, hroot, hauth, heq⟩ := hs
  refine ⟨(bankValidRootedReferenceData ring hbank).referenceNext z e,
    e :: history, ?_, ?_, ?_⟩
  · exact bankReferenceRootedStep ring hn hbank z e hroot
  · exact inheritedAuthorityExtinctStep ring hbank z hauth e
  · rw [heq]
    exact (bankStageDrainReferenceStep ring
      (by omega : 2 ≤ n) hbank z hauth history e).symm

/-- The precise projected-domain replacement for the
all-Cartesian-state certificate. It does NOT assert an inhabitant.

The rank is a global state function, but its nominated drop and
all-edge nonincrease are required ONLY on the closed protected
extinct-reference projection. Its initial budget is unchanged. -/
def BankExtinctGrantDrainProtectedRankCertificate {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (history : List (Fin n)) : Prop :=
  ∃ (rank : GrantDrainState n
        (BankReferenceState ring hbank) → Nat)
    (chosen : GrantDrainState n
        (BankReferenceState ring hbank) → Fin n),
    (∀ s : GrantDrainState n (BankReferenceState ring hbank),
      BankExtinctDrainProtectedDomain ring hbank s →
      ¬ GrantFree s →
        rank (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          s (chosen s)) + 1 ≤ rank s) ∧
    (∀ s : GrantDrainState n (BankReferenceState ring hbank),
      BankExtinctDrainProtectedDomain ring hbank s →
      ¬ GrantFree s → ∀ e : Fin n,
        rank (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank)
          s e) ≤ rank s) ∧
    n * rank (bankStageDrainProjection ring hbank z history) ≤
      grantDrainCeiling n

/-- Conditional sigma_G transfer using the RESTRICTED nominated
Bellman lemma. All protected and extinction assumptions are explicit.
The missing machine-specific rank certificate remains a hypothesis. -/
theorem bankExtinctGrantDrainCeilingCostOfProtectedRank {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hroot : headlineRooted ring z.val.1)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (history : List (Fin n))
    (hcertificate :
      BankExtinctGrantDrainProtectedRankCertificate
        ring hbank z history)
    (T : Nat) :
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T ≤
      n ^ T * grantDrainCeiling n := by
  obtain ⟨rank, chosen, hdrop, hnoninc, hbudget⟩ := hcertificate
  have hclosed :
      ∀ s : GrantDrainState n (BankReferenceState ring hbank),
        BankExtinctDrainProtectedDomain ring hbank s →
        ¬ GrantFree s → ∀ e : Fin n,
        BankExtinctDrainProtectedDomain ring hbank
          (grantDrainStep ring
            (bankStageDrainFresh ring hbank)
            (bankStageDrainScratchNext ring hbank) s e) := by
    intro s hs _ e
    exact bankExtinctDrainProtectedDomainClosed ring hn hbank s hs e
  have hinitial :
      BankExtinctDrainProtectedDomain ring hbank
        (bankStageDrainProjection ring hbank z history) :=
    ⟨z, history, hroot, hauth, rfl⟩
  have hbound :=
    L3.Prob.costNumerator_le_of_nominated_edge_on
      (grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank))
      (fun s : GrantDrainState n
        (BankReferenceState ring hbank) => GrantFree s)
      (BankExtinctDrainProtectedDomain ring hbank)
      rank chosen hclosed hdrop hnoninc
      (bankStageDrainProjection ring hbank z history)
      hinitial T
  calc
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => NativeLiftGrantFree a.val.1) z T ≤
      costNumerator
        (grantDrainStep ring
          (bankStageDrainFresh ring hbank)
          (bankStageDrainScratchNext ring hbank))
        (fun s : GrantDrainState n
          (BankReferenceState ring hbank) => GrantFree s)
        (bankStageDrainProjection ring hbank z history) T :=
      bankStageDrainCostNumeratorLe
        ring (by omega : 2 ≤ n) hbank z hauth history T
    _ ≤ n ^ T *
        (n * rank (bankStageDrainProjection ring hbank z history)) :=
      hbound
    _ ≤ n ^ T * grantDrainCeiling n :=
      Nat.mul_le_mul_left _ hbudget

end L3.RenewalReferenceClock


/-!
Finite-word lower tail for a nominated edge, and finite-label union.

The existing
import closure does not directly expose L3.GrantDiscrete.nominatedMoves.
Consequently the exact recursion is taken as explicit hypotheses
hzero and hcons. The actual nominatedMoves satisfies these equations
definitionally when both modules are visible to the importing caller.
No import, protocol transition, or existing theorem is changed.

The weight is 1 on the nominated letter and 2 on other letters.
Its exact mass is (2*n-1)^T even for state-dependent nominations.
The integer inequality 2*(2*n-1)^(2*n) <= (2*n)^(2*n) supplies decay.
-/

namespace L3.RenewalReferenceClock

open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

private def grantTailMissWeight {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n) :
    S → List (Fin n) → Nat
  | _, [] => 1
  | x, e :: es =>
      (if e = chosen x then 1 else 2) *
        grantTailMissWeight next chosen (next x e) es

private theorem grantTailEdgeWeight {n : Nat} (a : Fin n) :
    (List.ofFn (fun e : Fin n => if e = a then 1 else 2)).sum =
      2 * n - 1 := by
  induction n with
  | zero =>
      exact Fin.elim0 a
  | succ n ih =>
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then 1 else 2)).sum =
              n * 2 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then 1 else 2)
            (fun _ : Fin n => 2)
            (by
              intro i
              have hne : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hne])
          rw [hh, ofFn_sum_const]
        rw [if_pos rfl, ht]
        omega
      · intro b
        rw [List.ofFn_succ, List.sum_cons]
        have hne : (0 : Fin (n + 1)) ≠ b.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = b.val + 1 at hv
          omega
        rw [if_neg hne]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = b.succ then 1 else 2)
          (fun i : Fin n => if i = b then 1 else 2)
          (by
            intro i
            simp only [Fin.succ_inj])
        rw [hh, ih b]
        have hb := b.isLt
        omega

private theorem grantTailScheduleMul {n : Nat} (T c : Nat)
    (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => c * f w) =
      c * L3.Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => c * f w) =
    c * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => c * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ofFn_sum_mul_left]

private theorem grantTailMass {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (x : S) (T : Nat) (hn : 0 < n) :
    L3.Prob.scheduleSum n T
      (fun w => grantTailMissWeight next chosen x w) =
        (2 * n - 1) ^ T := by
  induction T generalizing x with
  | zero =>
      simp [L3.Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules, grantTailMissWeight]
  | succ T ih =>
      have hrow (e : Fin n) :
          L3.Prob.scheduleSum n T
            (fun w => grantTailMissWeight next chosen x (e :: w)) =
          (if e = chosen x then 1 else 2) * (2 * n - 1) ^ T := by
        calc
          _ = L3.Prob.scheduleSum n T
                (fun w => (if e = chosen x then 1 else 2) *
                  grantTailMissWeight next chosen (next x e) w) := rfl
          _ = (if e = chosen x then 1 else 2) *
                L3.Prob.scheduleSum n T
                  (fun w => grantTailMissWeight next chosen (next x e) w) :=
                grantTailScheduleMul T _ _
          _ = (if e = chosen x then 1 else 2) *
                (2 * n - 1) ^ T := by
                rw [ih (next x e)]
      calc
        L3.Prob.scheduleSum n (T + 1)
            (fun w => grantTailMissWeight next chosen x w) =
          (List.ofFn (fun e : Fin n =>
            L3.Prob.scheduleSum n T
              (fun w => grantTailMissWeight next chosen x (e :: w)))).sum :=
            FixedSpanRenewalPayload.wordSum_succ n T _
        _ = (List.ofFn (fun e : Fin n =>
              (if e = chosen x then 1 else 2) *
                (2 * n - 1) ^ T)).sum :=
            ofFn_sum_eq _ _ hrow
        _ = (List.ofFn (fun e : Fin n =>
              (2 * n - 1) ^ T *
                (if e = chosen x then 1 else 2))).sum :=
            ofFn_sum_eq _ _ (fun e => Nat.mul_comm _ _)
        _ = (2 * n - 1) ^ T *
              (List.ofFn (fun e : Fin n =>
                if e = chosen x then 1 else 2)).sum := by
            rw [ofFn_sum_mul_left]
        _ = (2 * n - 1) ^ T * (2 * n - 1) := by
            rw [grantTailEdgeWeight]
        _ = (2 * n - 1) ^ (T + 1) := by
            rw [Nat.pow_succ]

private theorem grantTailHitsProduct {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (w : List (Fin n)) :
    2 ^ (hits x w) * grantTailMissWeight next chosen x w =
      2 ^ w.length := by
  induction w generalizing x with
  | nil =>
      simp [hzero, grantTailMissWeight]
  | cons e es ih =>
      rw [hcons x e es]
      by_cases he : e = chosen x
      · simp only [if_pos he, grantTailMissWeight,
          List.length_cons, Nat.one_mul]
        have hadd :
            1 + hits (next x e) es = hits (next x e) es + 1 := by
          omega
        rw [hadd, Nat.pow_succ, Nat.pow_succ]
        calc
          (2 ^ hits (next x e) es * 2) *
              grantTailMissWeight next chosen (next x e) es =
            (2 ^ hits (next x e) es *
              grantTailMissWeight next chosen (next x e) es) * 2 := by
                ac_rfl
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]
      · simp only [if_neg he, grantTailMissWeight,
          List.length_cons, Nat.zero_add]
        rw [Nat.pow_succ]
        calc
          2 ^ hits (next x e) es *
              (2 * grantTailMissWeight next chosen (next x e) es) =
            (2 ^ hits (next x e) es *
              grantTailMissWeight next chosen (next x e) es) * 2 := by
                ac_rfl
          _ = 2 ^ es.length * 2 := by
                rw [ih (next x e)]

private theorem grantTailScheduleLengthMul {n : Nat}
    (T c : Nat) (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T
      (fun w => c ^ (w.length + 1) * f w) =
    c ^ (T + 1) * L3.Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun w => c ^ (w.length + 1) * f w) =
    c ^ (T + 1) * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => c ^ (w.length + 1) * f w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f]
  calc
    (List.ofFn (fun i : Fin (n ^ T) =>
        c ^ ((FixedSpanRenewalPayload.rawWord n T i).length + 1) *
          f (FixedSpanRenewalPayload.rawWord n T i))).sum =
      (List.ofFn (fun i : Fin (n ^ T) =>
        c ^ (T + 1) *
          f (FixedSpanRenewalPayload.rawWord n T i))).sum := by
        apply ofFn_sum_eq
        intro i
        rw [FixedSpanRenewalPayload.rawWord_length n T i]
    _ = c ^ (T + 1) *
          (List.ofFn (fun i : Fin (n ^ T) =>
            f (FixedSpanRenewalPayload.rawWord n T i))).sum := by
        rw [ofFn_sum_mul_left]

private theorem grantTailWeighted {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (T Q : Nat) (hn : 0 < n) :
    2 ^ (T + 1) *
      L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) ≤
      2 ^ Q * (2 * n - 1) ^ T := by
  have hpoint (w : List (Fin n)) :
      2 ^ (w.length + 1) *
        (if hits x w < Q then 1 else 0) ≤
      2 ^ Q * grantTailMissWeight next chosen x w := by
    by_cases h : hits x w < Q
    · have hpow : 2 * 2 ^ (hits x w) ≤ 2 ^ Q := by
        have hmono : 2 ^ (hits x w + 1) ≤ 2 ^ Q :=
          Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
        simpa only [Nat.pow_succ, Nat.mul_comm] using hmono
      simp only [if_pos h, Nat.mul_one]
      calc
        2 ^ (w.length + 1) =
          (2 * 2 ^ (hits x w)) *
            grantTailMissWeight next chosen x w := by
              rw [Nat.pow_succ,
                ← grantTailHitsProduct next chosen hits hzero hcons x w]
              ac_rfl
        _ ≤ 2 ^ Q * grantTailMissWeight next chosen x w :=
          Nat.mul_le_mul_right _ hpow
    · simp [h]
  calc
    2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w => if hits x w < Q then 1 else 0) =
      L3.Prob.scheduleSum n T
        (fun w => 2 ^ (w.length + 1) *
          (if hits x w < Q then 1 else 0)) :=
        (grantTailScheduleLengthMul T 2 _).symm
    _ ≤ L3.Prob.scheduleSum n T
          (fun w => 2 ^ Q * grantTailMissWeight next chosen x w) :=
        L3.Density.schedule_sum_mono T _ _ hpoint
    _ = 2 ^ Q * (2 * n - 1) ^ T := by
        rw [grantTailScheduleMul, grantTailMass next chosen x T hn]

private theorem grantTailLinearPower (a k : Nat) :
    a ^ k * (a + 1 + k) ≤ (a + 1) ^ (k + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hp : a ^ (k + 1) ≤ (a + 1) ^ (k + 1) :=
        Nat.pow_le_pow_left (Nat.le_succ a) (k + 1)
      calc
        a ^ (k + 1) * (a + 1 + (k + 1)) =
          (a ^ k * (a + 1 + k)) * a + a ^ (k + 1) := by
            have hc : a + 1 + (k + 1) = a + 1 + k + 1 := by
              omega
            rw [hc]
            simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one,
              Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ (a + 1) ^ (k + 1) * a +
              (a + 1) ^ (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right a ih) hp
        _ = (a + 1) ^ ((k + 1) + 1) := by
          rw [Nat.pow_succ (a + 1) (k + 1), Nat.mul_add, Nat.mul_one]

private theorem grantTailHalfBlock (n : Nat) (hn : 0 < n) :
    2 * (2 * n - 1) ^ (2 * n) ≤ (2 * n) ^ (2 * n) := by
  have he : (2 * n - 1) + 1 = 2 * n := by
    omega
  have hpow :
      (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) := by
    calc
      (2 * n - 1) ^ (2 * n) =
          (2 * n - 1) ^ ((2 * n - 1) + 1) := by
            rw [he]
      _ = (2 * n - 1) ^ (2 * n - 1) * (2 * n - 1) :=
        Nat.pow_succ _ _
  calc
    2 * (2 * n - 1) ^ (2 * n) =
        (2 * n - 1) ^ (2 * n - 1) * (2 * (2 * n - 1)) := by
          rw [hpow]
          ac_rfl
    _ ≤ (2 * n - 1) ^ (2 * n - 1) *
        ((2 * n - 1) + 1 + (2 * n - 1)) :=
          Nat.mul_le_mul_left _ (by omega)
    _ ≤ ((2 * n - 1) + 1) ^ ((2 * n - 1) + 1) :=
          grantTailLinearPower _ _
    _ = (2 * n) ^ (2 * n) := by
          rw [he]

private theorem grantTailDecay (n T Q : Nat) (hn : 0 < n)
    (hT : 2 * n * Q ≤ T) :
    2 ^ Q * (2 * n - 1) ^ T ≤ (2 * n) ^ T := by
  have hblock := grantTailHalfBlock n hn
  have hpower :
      (2 * (2 * n - 1) ^ (2 * n)) ^ Q ≤
        ((2 * n) ^ (2 * n)) ^ Q :=
    Nat.pow_le_pow_left hblock Q
  have hblocks :
      2 ^ Q * (2 * n - 1) ^ (2 * n * Q) ≤
        (2 * n) ^ (2 * n * Q) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using hpower
  have hsplit : 2 * n * Q + (T - 2 * n * Q) = T := by
    omega
  calc
    2 ^ Q * (2 * n - 1) ^ T =
        (2 ^ Q * (2 * n - 1) ^ (2 * n * Q)) *
          (2 * n - 1) ^ (T - 2 * n * Q) := by
            rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
    _ ≤ (2 * n) ^ (2 * n * Q) *
          (2 * n) ^ (T - 2 * n * Q) :=
        Nat.mul_le_mul hblocks
          (Nat.pow_le_pow_left
            (by omega : 2 * n - 1 ≤ 2 * n) (T - 2 * n * Q))
    _ = (2 * n) ^ T := by
        rw [← Nat.pow_add, hsplit]

/-- One-label lower tail. hits has precisely nominatedMoves recursion. -/
theorem nominatedHits_lower_tail_half {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n)
    (hits : S → List (Fin n) → Nat)
    (hzero : ∀ y : S, hits y [] = 0)
    (hcons : ∀ (y : S) (e : Fin n) (es : List (Fin n)),
      hits y (e :: es) =
        (if e = chosen y then 1 else 0) + hits (next y e) es)
    (x : S) (T Q : Nat) (hn : 0 < n)
    (hT : 2 * n * Q + n ≤ T) :
    L3.Prob.scheduleSum n T
      (fun w => if hits x w < Q then 1 else 0) * 2 ≤ n ^ T := by
  have hw := grantTailWeighted next chosen hits hzero hcons x T Q hn
  have hdecay : 2 ^ Q * (2 * n - 1) ^ T ≤ (2 * n) ^ T :=
    grantTailDecay n T Q hn (by omega)
  have hbound :
      2 ^ (T + 1) * L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) ≤
        (2 * n) ^ T :=
    Nat.le_trans hw hdecay
  have hscaled :
      2 ^ T *
        (2 * L3.Prob.scheduleSum n T
          (fun w => if hits x w < Q then 1 else 0)) ≤
      2 ^ T * n ^ T := by
    calc
      _ = 2 ^ (T + 1) * L3.Prob.scheduleSum n T
            (fun w => if hits x w < Q then 1 else 0) := by
              rw [Nat.pow_succ]
              ac_rfl
      _ ≤ (2 * n) ^ T := hbound
      _ = 2 ^ T * n ^ T := by
          rw [Nat.mul_pow]
  have hcancel :
      2 * L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) ≤ n ^ T :=
    Nat.le_of_mul_le_mul_left hscaled
      (Nat.pow_pos (by decide : 0 < (2 : Nat)))
  calc
    L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) * 2 =
      2 * L3.Prob.scheduleSum n T
        (fun w => if hits x w < Q then 1 else 0) :=
      Nat.mul_comm _ _
    _ ≤ n ^ T := hcancel

private theorem grantTailFamilyIndicator :
    ∀ (d : Nat) (b : Fin d → Bool),
      (if (List.ofFn b).any (fun z => z) then 1 else 0) ≤
        (List.ofFn (fun i : Fin d => if b i then 1 else 0)).sum := by
  intro d
  induction d with
  | zero =>
      intro b
      simp
  | succ d ih =>
      intro b
      cases hb : b (0 : Fin (d + 1)) with
      | false =>
          simpa [List.ofFn_succ, hb] using
            ih (fun i : Fin d => b i.succ)
      | true =>
          simp [List.ofFn_succ, hb]

/-- Union over labels on the same physical word, without independence. -/
theorem nominatedHits_family_lower_tail_half
    {S : Type} {n d : Nat}
    (next : S → Fin n → S)
    (chosen : Fin d → S → Fin n)
    (hits : Fin d → S → List (Fin n) → Nat)
    (hzero : ∀ (i : Fin d) (y : S), hits i y [] = 0)
    (hcons : ∀ (i : Fin d) (y : S) (e : Fin n)
      (es : List (Fin n)),
      hits i y (e :: es) =
        (if e = chosen i y then 1 else 0) +
          hits i (next y e) es)
    (x : S) (T Q : Nat) (hn : 0 < n)
    (hT : 2 * n * Q + n ≤ T) :
    L3.Prob.scheduleSum n T
      (fun w =>
        if (List.ofFn (fun i : Fin d =>
          decide (hits i x w < Q))).any (fun z => z)
        then 1 else 0) * 2 ≤ d * n ^ T := by
  have hpoint (w : List (Fin n)) :
      (if (List.ofFn (fun i : Fin d =>
          decide (hits i x w < Q))).any (fun z => z)
       then 1 else 0) ≤
      (List.ofFn (fun i : Fin d =>
        if hits i x w < Q then 1 else 0)).sum := by
    calc
      _ ≤ (List.ofFn (fun i : Fin d =>
            if decide (hits i x w < Q) then 1 else 0)).sum :=
          grantTailFamilyIndicator d
            (fun i : Fin d => decide (hits i x w < Q))
      _ = (List.ofFn (fun i : Fin d =>
            if hits i x w < Q then 1 else 0)).sum := by
          apply ofFn_sum_eq
          intro i
          by_cases hi : hits i x w < Q
          · simp [hi]
          · simp [hi]
  have hmono := L3.Density.schedule_sum_mono T
    (fun w : List (Fin n) =>
      if (List.ofFn (fun i : Fin d =>
        decide (hits i x w < Q))).any (fun z => z)
      then 1 else 0)
    (fun w : List (Fin n) =>
      (List.ofFn (fun i : Fin d =>
        if hits i x w < Q then 1 else 0)).sum)
    hpoint
  have htwo :
      2 * L3.Prob.scheduleSum n T
        (fun w =>
          if (List.ofFn (fun i : Fin d =>
            decide (hits i x w < Q))).any (fun z => z)
          then 1 else 0) ≤ d * n ^ T := by
    calc
      _ ≤ 2 * L3.Prob.scheduleSum n T
            (fun w =>
              (List.ofFn (fun i : Fin d =>
                if hits i x w < Q then 1 else 0)).sum) :=
          Nat.mul_le_mul_left _ hmono
      _ = (List.ofFn (fun i : Fin d =>
            2 * L3.Prob.scheduleSum n T
              (fun w => if hits i x w < Q then 1 else 0))).sum := by
          rw [L3.Density.schedule_sum_fin, ← ofFn_sum_mul_left]
      _ ≤ d * n ^ T := by
          have hs :
              (List.ofFn (fun i : Fin d =>
                2 * L3.Prob.scheduleSum n T
                  (fun w => if hits i x w < Q then 1 else 0))).sum ≤
              (List.ofFn (fun _ : Fin d => n ^ T)).sum :=
            ofFn_sum_le _ _ (fun i => by
              have hi := nominatedHits_lower_tail_half
                next (chosen i) (hits i)
                (hzero i) (hcons i) x T Q hn hT
              calc
                2 * L3.Prob.scheduleSum n T
                    (fun w => if hits i x w < Q then 1 else 0) =
                  L3.Prob.scheduleSum n T
                    (fun w => if hits i x w < Q then 1 else 0) * 2 :=
                  Nat.mul_comm _ _
                _ ≤ n ^ T := hi)
          simpa only [ofFn_sum_const] using hs
  calc
    L3.Prob.scheduleSum n T
        (fun w =>
          if (List.ofFn (fun i : Fin d =>
            decide (hits i x w < Q))).any (fun z => z)
          then 1 else 0) * 2 =
      2 * L3.Prob.scheduleSum n T
        (fun w =>
          if (List.ofFn (fun i : Fin d =>
            decide (hits i x w < Q))).any (fun z => z)
          then 1 else 0) := Nat.mul_comm _ _
    _ ≤ d * n ^ T := htwo

end L3.RenewalReferenceClock


/-!
Generic quota-to-first-hit and restart accounting.

For a surviving word, its nominated hits are exactly the hits before
the first occurrence of P. We apply the full-word recursion:
only surviving words need be compared with the quota accounting.

At T >= 2*n*Q+n, the union over d labels loses a factor d.
The stronger second quota bound absorbs that factor by taking
T >= 2*n*(Q+d)+n; the linear d is a deliberately conservative
integer replacement for a logarithmic padding.

The restart lemma uses the existing Density.costNumerator_of_block
with an absorbing barrier outside I or after reaching P. This avoids
assuming that the original predicate P is closed.
-/

namespace L3.RenewalReferenceClock

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

private def grantQuotaRun {S : Type} {n : Nat}
    (next : S → Fin n → S) : S → List (Fin n) → S
  | x, [] => x
  | x, e :: es => grantQuotaRun next (next x e) es

private def grantQuotaHits {S : Type} {n : Nat}
    (next : S → Fin n → S) (chosen : S → Fin n) :
    S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: es =>
      (if e = chosen x then 1 else 0) +
        grantQuotaHits next chosen (next x e) es

private theorem grantQuotaRunClosed {S : Type} {n : Nat}
    (next : S → Fin n → S) (I : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e)) :
    ∀ (x : S) (w : List (Fin n)), I x →
      I (grantQuotaRun next x w) := by
  intro x w
  induction w generalizing x with
  | nil =>
      intro hx
      exact hx
  | cons e es ih =>
      intro hx
      exact ih (next x e) (hc x hx e)

private theorem grantQuotaSurvivalBit {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      UniformFirstHit.survivalWord next P x w ≤ 1 := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simp [UniformFirstHit.survivalWord, hp]
  | cons e es ih =>
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp]
      · simpa only [UniformFirstHit.survivalWord, if_neg hp] using
          ih (next x e)

private theorem grantQuotaSurvivalEndNot {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) :
    ∀ (x : S) (w : List (Fin n)),
      UniformFirstHit.survivalWord next P x w = 1 →
      ¬ P (grantQuotaRun next x w) := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      intro hs hp
      simp [UniformFirstHit.survivalWord] at hs
      exact hs hp
  | cons e es ih =>
      intro hs
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp] at hs
      · have htail :
            UniformFirstHit.survivalWord next P (next x e) es = 1 := by
          simpa only [UniformFirstHit.survivalWord, if_neg hp] using hs
        exact ih (next x e) htail

/-- On an unhit path ending with positive quota, each nominated edge
is charged to a unit of initial quota; all other edges cost nothing. -/
private theorem grantQuotaCharge {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (q : S → Nat) (chosen : S → Fin n)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (hmono : ∀ x, I x → ¬ P x → ∀ e, q (next x e) ≤ q x)
    (hdrop : ∀ x, I x → ¬ P x → 0 < q x →
      q (next x (chosen x)) + 1 ≤ q x) :
    ∀ (x : S) (w : List (Fin n)),
      I x →
      UniformFirstHit.survivalWord next P x w = 1 →
      0 < q (grantQuotaRun next x w) →
      grantQuotaHits next chosen x w +
        q (grantQuotaRun next x w) ≤ q x := by
  classical
  intro x w
  induction w generalizing x with
  | nil =>
      intro _ _ _
      simp [grantQuotaRun, grantQuotaHits]
  | cons e es ih =>
      intro hx hs hq
      by_cases hp : P x
      · simp [UniformFirstHit.survivalWord, hp] at hs
      · have htail :
            UniformFirstHit.survivalWord next P (next x e) es = 1 := by
          simpa only [UniformFirstHit.survivalWord, if_neg hp] using hs
        have hchild := ih (next x e) (hc x hx e) htail hq
        have hnoninc := hmono x hx hp e
        have hq' : 0 < q (grantQuotaRun next (next x e) es) := hq
        have hpos : 0 < q x := by omega
        have hedge :
            (if e = chosen x then 1 else 0) +
              q (next x e) ≤ q x := by
          by_cases he : e = chosen x
          · have hd : q (next x e) + 1 ≤ q x := by
              rw [he]
              exact hdrop x hx hp hpos
            simp only [if_pos he]
            omega
          · simp only [if_neg he, Nat.zero_add]
            exact hnoninc
        change (if e = chosen x then 1 else 0) +
            grantQuotaHits next chosen (next x e) es +
            q (grantQuotaRun next (next x e) es) ≤ q x
        omega

/-- Every surviving word belongs to the union of short-hit events.
The d=0 case is not excluded: then all-zero quota forces P. -/
private theorem grantQuotaSurvivalUnion
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (hmono : ∀ x, I x → ¬ P x → ∀ i e,
      quota i (next x e) ≤ quota i x)
    (hdrop : ∀ x, I x → ¬ P x → ∀ i,
      0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (hzero : ∀ x, I x → (∀ i : Fin d, quota i x = 0) → P x)
    (x : S) (hx : I x) (Q : Nat)
    (hbudget : ∀ i : Fin d, quota i x ≤ Q)
    (w : List (Fin n)) :
    UniformFirstHit.survivalWord next P x w ≤
      (if (List.ofFn (fun i : Fin d =>
        decide (grantQuotaHits next (chosen i) x w < Q))).any
          (fun z => z)
       then 1 else 0) := by
  classical
  by_cases hs : UniformFirstHit.survivalWord next P x w = 1
  · have hIend : I (grantQuotaRun next x w) :=
      grantQuotaRunClosed next I hc x w hx
    have hNotEnd : ¬ P (grantQuotaRun next x w) :=
      grantQuotaSurvivalEndNot next P x w hs
    have hex :
        ∃ i : Fin d, 0 < quota i (grantQuotaRun next x w) := by
      by_cases he :
          ∃ i : Fin d, 0 < quota i (grantQuotaRun next x w)
      · exact he
      · have hall : ∀ i : Fin d,
            quota i (grantQuotaRun next x w) = 0 := by
          intro i
          have hnp : ¬ 0 < quota i (grantQuotaRun next x w) := by
            intro hi
            exact he ⟨i, hi⟩
          omega
        exact False.elim (hNotEnd
          (hzero (grantQuotaRun next x w) hIend hall))
    obtain ⟨i, hipos⟩ := hex
    have hcharge :
        grantQuotaHits next (chosen i) x w +
          quota i (grantQuotaRun next x w) ≤ quota i x :=
      grantQuotaCharge next I P (quota i) (chosen i) hc
        (fun y hy hn e => hmono y hy hn i e)
        (fun y hy hn hpos => hdrop y hy hn i hpos)
        x w hx hs hipos
    have hsmall : grantQuotaHits next (chosen i) x w < Q := by
      have hbound := hbudget i
      omega
    have hany :
        (List.ofFn (fun j : Fin d =>
          decide (grantQuotaHits next (chosen j) x w < Q))).any
            (fun z => z) = true := by
      rw [List.any_eq_true]
      exact ⟨true, List.mem_ofFn.mpr ⟨i, by simp [hsmall]⟩, rfl⟩
    simp [hs, hany]
  · have hz :
        UniformFirstHit.survivalWord next P x w = 0 := by
      have hb := grantQuotaSurvivalBit next P x w
      omega
    simp [hz]

/-- Quota-to-hitting, exact d-label union cost. This is not a
half-probability bound for d > 1 at the same horizon. -/
theorem grantQuota_family_survival_mass
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (hmono : ∀ x, I x → ¬ P x → ∀ i e,
      quota i (next x e) ≤ quota i x)
    (hdrop : ∀ x, I x → ¬ P x → ∀ i,
      0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (hzero : ∀ x, I x → (∀ i : Fin d, quota i x = 0) → P x)
    (x : S) (hx : I x) (Q T : Nat)
    (hbudget : ∀ i : Fin d, quota i x ≤ Q)
    (hn : 0 < n) (hT : 2 * n * Q + n ≤ T) :
    2 * UniformFirstHit.survivalNumerator next P x T ≤
      d * n ^ T := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord next P x w ≤
      (if (List.ofFn (fun i : Fin d =>
        decide (grantQuotaHits next (chosen i) x w < Q))).any
          (fun z => z)
       then 1 else 0) :=
    grantQuotaSurvivalUnion next I P quota chosen hc hmono hdrop
      hzero x hx Q hbudget w
  have hmass :
      UniformFirstHit.survivalNumerator next P x T ≤
      L3.Prob.scheduleSum n T
        (fun w =>
          if (List.ofFn (fun i : Fin d =>
            decide (grantQuotaHits next (chosen i) x w < Q))).any
              (fun z => z)
          then 1 else 0) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord next P x) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  calc
    2 * UniformFirstHit.survivalNumerator next P x T ≤
        2 * L3.Prob.scheduleSum n T
          (fun w =>
            if (List.ofFn (fun i : Fin d =>
              decide (grantQuotaHits next (chosen i) x w < Q))).any
                (fun z => z)
            then 1 else 0) :=
      Nat.mul_le_mul_left _ hmass
    _ = L3.Prob.scheduleSum n T
          (fun w =>
            if (List.ofFn (fun i : Fin d =>
              decide (grantQuotaHits next (chosen i) x w < Q))).any
                (fun z => z)
            then 1 else 0) * 2 :=
      Nat.mul_comm _ _
    _ ≤ d * n ^ T := by
      exact nominatedHits_family_lower_tail_half next chosen
        (fun i => grantQuotaHits next (chosen i))
        (by intro i y; rfl)
        (by intro i y e es; rfl) x T Q hn hT

private theorem grantQuotaLabelLePow (d : Nat) : d ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hp : 0 < (2 : Nat) ^ d :=
        Nat.pow_pos (by decide : 0 < (2 : Nat))
      rw [Nat.pow_succ]
      omega

/-- The d-label loss is absorbed by d extra halving blocks,
with a conservative (rather than logarithmic) horizon. -/
theorem grantQuota_family_survival_half
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (quota : Fin d → S → Nat)
    (chosen : Fin d → S → Fin n)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (hmono : ∀ x, I x → ¬ P x → ∀ i e,
      quota i (next x e) ≤ quota i x)
    (hdrop : ∀ x, I x → ¬ P x → ∀ i,
      0 < quota i x →
      quota i (next x (chosen i x)) + 1 ≤ quota i x)
    (hzero : ∀ x, I x → (∀ i : Fin d, quota i x = 0) → P x)
    (x : S) (hx : I x) (Q T : Nat)
    (hbudget : ∀ i : Fin d, quota i x ≤ Q)
    (hn : 0 < n) (hT : 2 * n * (Q + d) + n ≤ T) :
    2 * UniformFirstHit.survivalNumerator next P x T ≤
      n ^ T := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord next P x w ≤
      (List.ofFn (fun i : Fin d =>
        if grantQuotaHits next (chosen i) x w < Q then 1 else 0)).sum := by
    calc
      _ ≤ (if (List.ofFn (fun i : Fin d =>
            decide (grantQuotaHits next (chosen i) x w < Q))).any
              (fun z => z)
          then 1 else 0) :=
        grantQuotaSurvivalUnion next I P quota chosen hc hmono hdrop
          hzero x hx Q hbudget w
      _ ≤ (List.ofFn (fun i : Fin d =>
            if decide (grantQuotaHits next (chosen i) x w < Q)
            then 1 else 0)).sum :=
        grantTailFamilyIndicator d
          (fun i : Fin d =>
            decide (grantQuotaHits next (chosen i) x w < Q))
      _ = (List.ofFn (fun i : Fin d =>
            if grantQuotaHits next (chosen i) x w < Q then 1 else 0)).sum := by
        apply ofFn_sum_eq
        intro i
        by_cases hi : grantQuotaHits next (chosen i) x w < Q
        · simp [hi]
        · simp [hi]
  have hmass :
      UniformFirstHit.survivalNumerator next P x T ≤
      L3.Prob.scheduleSum n T
        (fun w => (List.ofFn (fun i : Fin d =>
          if grantQuotaHits next (chosen i) x w < Q
          then 1 else 0)).sum) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord next P x) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  have hrow (i : Fin d) :
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w =>
            if grantQuotaHits next (chosen i) x w < Q then 1 else 0) ≤
      2 ^ Q * (2 * n - 1) ^ T :=
    grantTailWeighted next (chosen i)
      (grantQuotaHits next (chosen i))
      (by intro y; rfl)
      (by intro y e es; rfl) x T Q hn
  have hweighted :
      2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator next P x T ≤
      d * (2 ^ Q * (2 * n - 1) ^ T) := by
    calc
      _ ≤ 2 ^ (T + 1) *
            L3.Prob.scheduleSum n T
              (fun w => (List.ofFn (fun i : Fin d =>
                if grantQuotaHits next (chosen i) x w < Q
                then 1 else 0)).sum) :=
          Nat.mul_le_mul_left _ hmass
      _ = (List.ofFn (fun i : Fin d =>
            2 ^ (T + 1) *
              L3.Prob.scheduleSum n T
                (fun w =>
                  if grantQuotaHits next (chosen i) x w < Q
                  then 1 else 0))).sum := by
          rw [L3.Density.schedule_sum_fin, ← ofFn_sum_mul_left]
      _ ≤ (List.ofFn (fun _ : Fin d =>
            2 ^ Q * (2 * n - 1) ^ T)).sum :=
          ofFn_sum_le _ _ hrow
      _ = d * (2 ^ Q * (2 * n - 1) ^ T) :=
          ofFn_sum_const _ _
  have hcoef :
      d * (2 ^ Q * (2 * n - 1) ^ T) ≤
      2 ^ (Q + d) * (2 * n - 1) ^ T := by
    calc
      _ = (d * 2 ^ Q) * (2 * n - 1) ^ T := by ac_rfl
      _ ≤ (2 ^ d * 2 ^ Q) * (2 * n - 1) ^ T :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (grantQuotaLabelLePow d))
      _ = 2 ^ (Q + d) * (2 * n - 1) ^ T := by
        rw [Nat.pow_add]
        ac_rfl
  have hdecay :
      2 ^ (Q + d) * (2 * n - 1) ^ T ≤ (2 * n) ^ T :=
    grantTailDecay n T (Q + d) hn (by omega)
  have hfinal :
      2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator next P x T ≤ (2 * n) ^ T :=
    Nat.le_trans (Nat.le_trans hweighted hcoef) hdecay
  have hscaled :
      2 ^ T *
        (2 * UniformFirstHit.survivalNumerator next P x T) ≤
      2 ^ T * n ^ T := by
    calc
      _ = 2 ^ (T + 1) *
            UniformFirstHit.survivalNumerator next P x T := by
          rw [Nat.pow_succ]
          ac_rfl
      _ ≤ (2 * n) ^ T := hfinal
      _ = 2 ^ T * n ^ T := by
          rw [Nat.mul_pow]
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < (2 : Nat)))

/-! An absorbing barrier is needed only for the generic restart
interface; the original physical step is kept in the conclusion. -/

private def grantRestartGood {S : Type}
    (I P : S → Prop) (x : S) : Prop :=
  P x ∨ ¬ I x

private noncomputable def grantRestartNext {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (x : S) (e : Fin n) : S := by
  classical
  exact if grantRestartGood I P x then x else next x e

private theorem grantRestartGoodClosed {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop) :
    ∀ x e, grantRestartGood I P x →
      grantRestartGood I P (grantRestartNext next I P x e) := by
  classical
  intro x e hx
  change grantRestartGood I P
    (if grantRestartGood I P x then x else next x e)
  rw [if_pos hx]
  exact hx

private theorem grantRestartGoodAtIn {S : Type}
    (I P : S → Prop) (x : S) (hx : I x) :
    grantRestartGood I P x ↔ P x := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hnot => exact False.elim (hnot hx)
  · intro hp
    exact Or.inl hp

private theorem grantRestartWordEq {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e)) :
    ∀ T x, I x →
      wordSum (grantRestartNext next I P)
        (miss (grantRestartGood I P)) x T =
      UniformFirstHit.survivalNumerator next P x T := by
  classical
  have hgood := grantRestartGoodClosed next I P
  intro T
  induction T with
  | zero =>
      intro x hx
      by_cases hp : P x
      · rw [wordSum_zero,
          UniformFirstHit.survivalNumerator_of_target next P x hp 0]
        simp [miss, grantRestartGood, hp]
      · rw [wordSum_zero,
          UniformFirstHit.survivalNumerator_zero_of_not next P x hp]
        simp [miss, grantRestartGood, hp, hx]
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hg : grantRestartGood I P x := Or.inl hp
        rw [miss_zero (grantRestartNext next I P)
          (grantRestartGood I P) hgood x hg (T + 1),
          UniformFirstHit.survivalNumerator_of_target next P x hp (T + 1)]
      · have hg : ¬ grantRestartGood I P x := by
          intro hh
          exact hp ((grantRestartGoodAtIn I P x hx).mp hh)
        rw [wordSum_succ,
          UniformFirstHit.survivalNumerator_succ_of_not next P x hp T]
        apply ofFn_sum_eq
        intro e
        have hstep : grantRestartNext next I P x e = next x e := by
          unfold grantRestartNext
          exact if_neg hg
        rw [hstep]
        exact ih (next x e) (hc x hx e)

private theorem grantRestartCostEq {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e)) :
    ∀ T x, I x →
      costNumerator next P x T =
      costNumerator (grantRestartNext next I P)
        (grantRestartGood I P) x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hg : grantRestartGood I P x := Or.inl hp
        rw [costNumerator_terminal next P x hp (T + 1),
          costNumerator_terminal (grantRestartNext next I P)
            (grantRestartGood I P) x hg (T + 1)]
      · have hg : ¬ grantRestartGood I P x := by
          intro hh
          exact hp ((grantRestartGoodAtIn I P x hx).mp hh)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ (grantRestartNext next I P)
            (grantRestartGood I P) x hg T]
        exact congrArg (fun z : Nat => n ^ (T + 1) + z)
          (ofFn_sum_eq _ _ (fun e => by
            have hstep : grantRestartNext next I P x e =
                next x e := by
              unfold grantRestartNext
              exact if_neg hg
            rw [hstep]
            exact ih (next x e) (hc x hx e)))

/-- Uniform first-hit restart. The assumption is a half-failure
bound from every still-live state in the closed carrier I.
There is no assumption that P itself is absorbing.
L=0 is handled by its forced immediate-target consequence. -/
theorem grantRestart_cost_of_half_block {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (L : Nat)
    (hblock : ∀ x, I x → ¬ P x →
      2 * UniformFirstHit.survivalNumerator next P x L ≤ n ^ L)
    (x : S) (hx : I x) (T : Nat) :
    costNumerator next P x T ≤ n ^ T * (2 * L) := by
  classical
  cases L with
  | zero =>
      have hp : P x := by
        by_cases hpx : P x
        · exact hpx
        · have hh := hblock x hx hpx
          rw [UniformFirstHit.survivalNumerator_zero_of_not
            next P x hpx] at hh
          simp only [Nat.pow_zero, Nat.mul_one] at hh
          omega
      rw [costNumerator_terminal next P x hp T]
      exact Nat.zero_le _
  | succ L =>
      have hgood : ∀ y e, grantRestartGood I P y →
          grantRestartGood I P (grantRestartNext next I P y e) :=
        grantRestartGoodClosed next I P
      have hb : ∀ y,
          2 * wordSum (grantRestartNext next I P)
            (miss (grantRestartGood I P)) y (L + 1) ≤
          1 * n ^ (L + 1) := by
        intro y
        by_cases hg : grantRestartGood I P y
        · rw [miss_zero (grantRestartNext next I P)
            (grantRestartGood I P) hgood y hg (L + 1)]
          simp
        · have hy : I y := by
            by_cases hi : I y
            · exact hi
            · exact False.elim (hg (Or.inr hi))
          have hp : ¬ P y := by
            intro hpy
            exact hg (Or.inl hpy)
          rw [grantRestartWordEq next I P hc (L + 1) y hy]
          simpa only [Nat.one_mul] using hblock y hy hp
      have hceil :
          L3.Prob.renewalCeiling (L + 1) 1 2 = 2 * (L + 1) := by
        simp [L3.Prob.renewalCeiling, L3.Prob.ceilNat, Nat.mul_comm,
          Nat.mod_one]
      calc
        costNumerator next P x T =
          costNumerator (grantRestartNext next I P)
            (grantRestartGood I P) x T :=
          grantRestartCostEq next I P hc T x hx
        _ ≤ n ^ T * L3.Prob.renewalCeiling (L + 1) 1 2 :=
          L3.Density.costNumerator_of_block
            (grantRestartNext next I P)
            (grantRestartGood I P) (L + 1) 1 2
            (by omega) (by decide : 1 < (2 : Nat)) hgood hb x T
        _ = n ^ T * (2 * (L + 1)) := by
          rw [hceil]

end L3.RenewalReferenceClock


/-!
Proof-only initial-grant labels for the protected BANK drain.

The physical GrantDrainState has no
field recording grant ancestry.  Accordingly the Fin n family below is
a GHOST extension: label i denotes the grant initially at site i.
Labels may coalesce at one host.  A retired identity is never recycled.
No assertion that the ghost fidelity invariant is closed is made here.

Paper tokens.tex, lemma grant-drain: an OLD request chooses the outgoing
edge; otherwise choose the incoming edge.  Strong-lock quota starts at
the counterclockwise leader distance, weak-lock quota at 2*n, and an
OLD-request terminal quota at 1.  A stored remaining counter is debited
on each nominated edge for strong and weak labels.  The crucial assertion
that such counters never expire while an identity remains alive is
NOT proved; it is part of BankGrantLabelRemainingCases below.

The unconditional local physical result proved here is the leader
source sink: a surviving native source leader suppresses the old
source grant on that service.  The terminal OLD-request/leader
nomination therefore retires its label in one hit.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Paper classification. A live unmarked label carries no certified
drain quota and is excluded from the marked-domain hzero theorem. -/
inductive BankGrantMark where
  | unmarked
  | terminal
  | strong
  | weak
  deriving DecidableEq, Repr

/-- Exactly one proof-only identity per possible initial grant site. -/
structure BankGrantLabel (n : Nat) where
  host : Option (Fin n)
  mark : BankGrantMark
  remaining : Nat

/-- The projected BANK drain and a separate, non-physical label ledger. -/
structure BankGrantLabeledState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) where
  physical : GrantDrainState n (BankReferenceState ring hbank)
  labels : Fin n → BankGrantLabel n

/-- At a cut, exactly the initially occupied sites receive labels. -/
def bankGrantInitialLabels {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) (i : Fin n) : BankGrantLabel n :=
  { host := if s.grant i then some i else none
    mark := .unmarked
    remaining := 0 }

/-- Both directions matter: no fabricated identity, no uncovered grant. -/
def BankGrantLabeledCover {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) : Prop :=
  ∀ g : Fin n, s.physical.grant g = true ↔
    ∃ i : Fin n, (s.labels i).host = some g

theorem bankGrantInitialLabels_cover {n : Nat} {Scratch : Type}
    (s : GrantDrainState n Scratch) (g : Fin n) :
    s.grant g = true ↔
      ∃ i : Fin n, (bankGrantInitialLabels s i).host = some g := by
  constructor
  · intro hg
    exact ⟨g, by simp [bankGrantInitialLabels, hg]⟩
  · rintro ⟨i, hi⟩
    cases h : s.grant i with
    | false =>
        simp [bankGrantInitialLabels, h] at hi
    | true =>
        have hig : i = g := by
          simpa [bankGrantInitialLabels, h] using hi
        subst g
        exact h

/-- The zero-signal corridor [p,g), expressed without Finset.
The nearest counterclockwise leader is at distance d from g. -/
def BankGrantZeroCorridor {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Prop :=
  ∀ k : Nat, k < grantDrainLeftLeaderDistance ring s.native g →
    (s.native (PPL.shiftLeft ring g
      (grantDrainLeftLeaderDistance ring s.native g - k))).sg = false

/-- D.1: a protected, shielded source and a zero-signal corridor. -/
def BankGrantStrongLock {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Prop :=
  (s.native g).l = false ∧
  (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true ∧
  (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sh = true ∧
  BankGrantZeroCorridor ring s g

/-- D.1 with an unshielded source: the exceptional weak-lock case. -/
def BankGrantWeakLock {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : Prop :=
  (s.native g).l = false ∧
  (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).l = true ∧
  (s.native (PPL.shiftLeft ring g
    (grantDrainLeftLeaderDistance ring s.native g))).sh = false ∧
  BankGrantZeroCorridor ring s g

/-- Initial strong budget is the actual source distance, not n laps. -/
def bankGrantStrongLabel {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) : BankGrantLabel n :=
  { host := some g
    mark := .strong
    remaining := grantDrainLeftLeaderDistance ring s.native g }

/-- Initial weak budget pays at most one exceptional source death. -/
def bankGrantWeakLabel {n : Nat} (g : Fin n) : BankGrantLabel n :=
  { host := some g, mark := .weak, remaining := 2 * n }

/-- OLD-request terminal case: one nominated outgoing hit. -/
def bankGrantTerminalLabel {n : Nat} (g : Fin n) : BankGrantLabel n :=
  { host := some g, mark := .terminal, remaining := 1 }

/-- A retired identity has no host and consumes no budget. -/
def bankGrantRetiredLabel {n : Nat} : BankGrantLabel n :=
  { host := none, mark := .unmarked, remaining := 0 }

/-- A live certified label pays its remaining hit budget.
The unmarked constructor is intentionally excluded from certification. -/
def bankGrantLabelQuota {n : Nat} (a : BankGrantLabel n) : Nat :=
  match a.host with
  | none => 0
  | some _ =>
      match a.mark with
      | .unmarked => 0
      | .terminal => 1
      | .strong => a.remaining
      | .weak => a.remaining

def bankGrantQuota {n : Nat} {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) (i : Fin n) : Nat :=
  bankGrantLabelQuota (s.labels i)

/-- The literal old-request rule; retired labels nominate a fixed edge. -/
def bankGrantChosen {n : Nat} {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) (i : Fin n) : Fin n :=
  match (s.labels i).host with
  | none => i
  | some g =>
      if s.physical.request g then g else ring.leftNeighbor g

theorem bankGrantStrongLabel_quota {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (s : GrantDrainState n Scratch)
    (g : Fin n) :
    bankGrantLabelQuota (bankGrantStrongLabel ring s g) =
      grantDrainLeftLeaderDistance ring s.native g := by
  rfl

theorem bankGrantWeakLabel_quota {n : Nat} (g : Fin n) :
    bankGrantLabelQuota (bankGrantWeakLabel g) = 2 * n := by
  rfl

theorem bankGrantTerminalLabel_quota {n : Nat} (g : Fin n) :
    bankGrantLabelQuota (bankGrantTerminalLabel g) = 1 := by
  rfl

theorem bankGrantRetiredLabel_quota {n : Nat} :
    bankGrantLabelQuota (bankGrantRetiredLabel (n := n)) = 0 := by
  rfl

/-- Certificates also ensure that a living label has positive quota.
The weak tag may retain its at-most-2n counter after upgrading to a
strong lock; no new 2n allowance is allocated. -/
def BankGrantLabelGeometry {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) : Prop :=
  ∀ (i : Fin n) (g : Fin n),
    (s.labels i).host = some g →
    match (s.labels i).mark with
    | .unmarked => False
    | .terminal => s.physical.request g = true
    | .strong =>
        0 < (s.labels i).remaining ∧
        grantDrainLeftLeaderDistance ring s.physical.native g ≤
          (s.labels i).remaining ∧
        BankGrantStrongLock ring s.physical g
    | .weak =>
        0 < (s.labels i).remaining ∧
        (s.labels i).remaining ≤ 2 * n ∧
        (BankGrantWeakLock ring s.physical g ∨
          BankGrantStrongLock ring s.physical g)

/-- A marked/certified *ghost* cut above the actual protected
projected BANK domain. Unlike the physical domain alone, this
relation remembers initial-grant ancestry and remaining budgets. -/
def BankGrantMarkedProtectedDomain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank) : Prop :=
  BankExtinctDrainProtectedDomain ring hbank s.physical ∧
  BankGrantLabeledCover s ∧ BankGrantLabelGeometry s

/-- hzero for the exact n-label ledger. This uses coverage and
positive marked certificates; noncloning alone is insufficient to
reconstruct ancestry from a plain GrantDrainState. -/
theorem bankGrantMarked_zero_implies_GrantFree {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (hs : BankGrantMarkedProtectedDomain ring hbank s)
    (hz : ∀ i : Fin n, bankGrantQuota s i = 0) :
    GrantFree s.physical := by
  intro g
  cases hg : s.physical.grant g with
  | false =>
      rfl
  | true =>
      obtain ⟨i, hi⟩ := (hs.2.1 g).mp hg
      have hgeo := hs.2.2 i g hi
      have hzero : bankGrantLabelQuota (s.labels i) = 0 := hz i
      cases hm : (s.labels i).mark with
      | unmarked =>
          simp only [hm] at hgeo <;> exact False.elim hgeo
      | terminal =>
          simp [bankGrantLabelQuota, hi, hm] at hzero
      | strong =>
          simp only [hm] at hgeo
          have hp : 0 < (s.labels i).remaining := hgeo.1
          simp [bankGrantLabelQuota, hi, hm] at hzero
          omega
      | weak =>
          simp only [hm] at hgeo
          have hp : 0 < (s.labels i).remaining := hgeo.1
          simp [bankGrantLabelQuota, hi, hm] at hzero
          omega

/-!
The next definitions are a source-aware proposed ghost transport.
Unlike a test of the NEW grant bit alone, the old X identity is
retained only when its own old token has not been consumed/sunk;
a Y identity may join it at X.  A full coverage-preservation proof
is deliberately included among the outstanding cases.
-/

/-- Old-label transport through one actual no-producer token row. -/
private def bankGrantHostAdvance {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (host : Option (Fin n)) : Option (Fin n) :=
  match host with
  | none => none
  | some g =>
      if g = e then
        if s.grant e &&
            !(grantDrainNativeNext ring s e e).l &&
            !(grantDrainSelect ring s e == GrantDrainFire.leftLocal)
        then some e else none
      else if g = ring.rightNeighbor e then
        if (grantDrainTokenRow
              (s.request e) (s.grant e)
              (s.request (ring.rightNeighbor e))
              (s.grant (ring.rightNeighbor e))
              (grantDrainNativeNext ring s e e).l
              (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l
              false (grantDrainSelect ring s e)).2.grant
        then some (ring.rightNeighbor e)
        else if s.grant (ring.rightNeighbor e) &&
                !(s.request (ring.rightNeighbor e)) &&
                !(grantDrainNativeNext ring s e e).l &&
                !(grantDrainNativeNext ring s e (ring.rightNeighbor e)).l &&
                (grantDrainSelect ring s e == GrantDrainFire.none)
        then some e else none
      else some g

/-- The label quota is debited once per nominated edge. The
physical assertion that every still-live label has positive
remaining budget is NOT definitionally true; it needs lock geometry. -/
private def bankGrantSpend {n : Nat}
    (ring : DirectedRing n) (request : Fin n → Bool)
    (e : Fin n) (a : BankGrantLabel n) : Nat :=
  match a.mark with
  | .strong | .weak =>
      match a.host with
      | none => 0
      | some g =>
          if e = (if request g then g else ring.leftNeighbor g)
          then a.remaining - 1 else a.remaining
  | .unmarked | .terminal => a.remaining

private def bankGrantLabelAdvance {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (e : Fin n) (a : BankGrantLabel n) : BankGrantLabel n :=
  { a with
    host := bankGrantHostAdvance ring s e a.host
    remaining := bankGrantSpend ring s.request e a }

/-- Actual adapted projected drain paired with the proof-only ledger. -/
def bankGrantFamilyNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank) (e : Fin n) :
    BankGrantLabeledState ring hbank :=
  { physical := grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank) s.physical e
    labels := fun i => bankGrantLabelAdvance ring s.physical e (s.labels i) }

/-- A retired label can never be reintroduced by the host transport. -/
private theorem bankGrantHostAdvance_none {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    bankGrantHostAdvance ring s e none = none := rfl

theorem bankGrantRetired_quota_nonincrease {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (i e : Fin n)
    (hr : (s.labels i).host = none) :
    bankGrantQuota (bankGrantFamilyNext ring hbank s e) i ≤
      bankGrantQuota s i := by
  have ha :
      ((bankGrantFamilyNext ring hbank s e).labels i).host = none := by
    change bankGrantHostAdvance ring s.physical e (s.labels i).host = none
    rw [hr]
    exact bankGrantHostAdvance_none ring s.physical e
  have hleft :
      bankGrantQuota (bankGrantFamilyNext ring hbank s e) i = 0 := by
    simp only [bankGrantQuota, bankGrantLabelQuota, ha]
  have hright : bankGrantQuota s i = 0 := by
    simp only [bankGrantQuota, bankGrantLabelQuota, hr]
  rw [hleft, hright]
  exact Nat.le_refl 0

/-- The source leader bit is preserved by native E on the outgoing
edge. A post-E canonical birth may only keep or install that bit. -/
private theorem bankGrantNativeLeaderSource {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hl : (s.native e).l = true) :
    (grantDrainNativeNext ring s e e).l = true := by
  have he : (nativeE ring s.native e e).l = true := by
    simpa [nativeE, certLiteralEPair] using hl
  have hne : e ≠ ring.rightNeighbor e := by
    intro h
    exact EWord.rightNeighborDifferent ring hn e h.symm
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using he
  | leftLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hne] using he
  | cross =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]

/-- The source's final leader sink clears its old identity, even if
there was an independent old grant at the responder. -/
private theorem bankGrantHostAdvance_sourceLeader {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hl : (grantDrainNativeNext ring s e e).l = true) :
    bankGrantHostAdvance ring s e (some e) = none := by
  simp [bankGrantHostAdvance, hl]

/-- Independent literal-token check of the same source sink. -/
theorem bankGrantTokenRow_sourceLeaderSink
    (rx gx ry gy ly fresh : Bool) (fire : GrantDrainFire) :
    (grantDrainTokenRow rx gx ry gy true ly fresh fire).1.grant = false := by
  unfold grantDrainTokenRow
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases ly <;> cases fresh <;> cases fire <;> decide

/-- A native leader holding an OLD request and OLD grant nominates
its outgoing edge; on that edge its one-unit terminal quota vanishes.
This is a genuine physical source-leader case, not the full
follower OLD-request or leader-death dichotomy. -/
theorem bankGrantTerminalLeader_nominated_drop {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (i e : Fin n)
    (hhost : (s.labels i).host = some e)
    (hmark : (s.labels i).mark = BankGrantMark.terminal)
    (hreq : s.physical.request e = true)
    (hl : (s.physical.native e).l = true) :
    bankGrantChosen s i = e ∧
      bankGrantQuota (bankGrantFamilyNext ring hbank s e) i + 1 ≤
        bankGrantQuota s i := by
  have hnom : bankGrantChosen s i = e := by
    simp [bankGrantChosen, hhost, hreq]
  have hfinal :
      (grantDrainNativeNext ring s.physical e e).l = true :=
    bankGrantNativeLeaderSource ring hn s.physical e hl
  have hh :
      ((bankGrantFamilyNext ring hbank s e).labels i).host = none := by
    change bankGrantHostAdvance ring s.physical e (s.labels i).host = none
    rw [hhost]
    exact bankGrantHostAdvance_sourceLeader ring s.physical e hfinal
  have hafter :
      bankGrantQuota (bankGrantFamilyNext ring hbank s e) i = 0 := by
    simp only [bankGrantQuota, bankGrantLabelQuota, hh]
  have hbefore : bankGrantQuota s i = 1 := by
    simp [bankGrantQuota, bankGrantLabelQuota, hhost, hmark]
  constructor
  · exact hnom
  · rw [hafter, hbefore]
    decide

/-- The protected physical domain is closed, even
before the missing proof-only ancestry/lock closure is supplied. -/
theorem bankGrantPhysicalProtectedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (hs : BankGrantMarkedProtectedDomain ring hbank s)
    (e : Fin n) :
    BankExtinctDrainProtectedDomain ring hbank
      (bankGrantFamilyNext ring hbank s e).physical := by
  exact bankExtinctDrainProtectedDomainClosed
    ring hn hbank s.physical hs.1 e

/-- All remaining BANK-specific proof obligations in one named Prop.

(1) faithful ancestry is preserved by the exact token row, including
    coalescence, consumption, HOLD and sinks;
(2) the native strong/weak/terminal certificates and positive
    remaining budgets survive every edge (the one exceptional weak
    source death and closer births must be paid);
(3) the remaining terminal/follower and leader-deletion nomination
    cases make strict progress; and
(4) the common 2n label quota bound is maintained at marked cuts.

These clauses are NOT postulated as facts or proved by noncloning.
In particular the physical protected domain alone does not imply
the ghost domain is closed. -/
def BankGrantLabelRemainingCases {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  (∀ (s : BankGrantLabeledState ring hbank) (e : Fin n),
    BankGrantMarkedProtectedDomain ring hbank s →
      BankGrantLabeledCover (bankGrantFamilyNext ring hbank s e)) ∧
  (∀ (s : BankGrantLabeledState ring hbank) (e : Fin n),
    BankGrantMarkedProtectedDomain ring hbank s →
      BankGrantLabelGeometry (bankGrantFamilyNext ring hbank s e)) ∧
  (∀ (s : BankGrantLabeledState ring hbank) (i : Fin n),
    BankGrantMarkedProtectedDomain ring hbank s →
      ¬ GrantFree s.physical →
      0 < bankGrantQuota s i →
      bankGrantQuota
        (bankGrantFamilyNext ring hbank s (bankGrantChosen s i)) i + 1 ≤
          bankGrantQuota s i) ∧
  (∀ (s : BankGrantLabeledState ring hbank),
    BankGrantMarkedProtectedDomain ring hbank s →
      ∀ i : Fin n, bankGrantQuota s i ≤ 2 * n)

end L3.RenewalReferenceClock


/-!
Non-vacuity audit and exact cover transport.

The physical BANK reference is
unchanged. The initial ledger marks every occupied grant as unmarked
with zero quota. The marked geometry forbids a live unmarked
label, independently of any strong/weak lock geometry. Consequently
the original initialized ledger belongs to the marked protected
domain if and only if the physical cut is protected AND grant-free.

In contrast, cover preservation does not require any lock geometry:
the exact no-producer token row and the current proposed host map
preserve the equivalence between occupied slots and covered slots,
including HOLD, Y->X transport and merging. The proof below works
for any physical GrantDrainState at n >= 2. The n >= 2 hypothesis is
essential for the selected source and responder to be distinct.

These lemmas do NOT extend the marked domain to unmarked
labels, nor establish first-branch noncrossing or quota progress.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Initial bookkeeping is NOT a marked certificate. -/
def bankGrantInitialLabeledState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) :
    BankGrantLabeledState ring hbank :=
  { physical := s
    labels := bankGrantInitialLabels s }

theorem bankGrantInitialLabeled_cover {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) :
    BankGrantLabeledCover (bankGrantInitialLabeledState ring hbank s) := by
  intro g
  exact bankGrantInitialLabels_cover s g

/-- All initial quotas are zero, including when physical grants live. -/
theorem bankGrantInitial_all_quotas_zero {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) :
    ∀ i : Fin n,
      bankGrantQuota (bankGrantInitialLabeledState ring hbank s) i = 0 := by
  intro i
  cases hg : s.grant i with
  | false =>
      simp [bankGrantQuota, bankGrantLabelQuota,
        bankGrantInitialLabeledState, bankGrantInitialLabels, hg]
  | true =>
      simp [bankGrantQuota, bankGrantLabelQuota,
        bankGrantInitialLabeledState, bankGrantInitialLabels, hg]

/-- Exact obstruction: no initialized live grant can pass the
marked geometry, even when the grant's physical site is locked. -/
theorem bankGrantInitial_marked_iff_grantFree {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) :
    BankGrantMarkedProtectedDomain ring hbank
        (bankGrantInitialLabeledState ring hbank s) ↔
      BankExtinctDrainProtectedDomain ring hbank s ∧ GrantFree s := by
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    intro g
    cases hg : s.grant g with
    | false =>
        rfl
    | true =>
        have hh :
            ((bankGrantInitialLabeledState ring hbank s).labels g).host =
              some g := by
          simp [bankGrantInitialLabeledState, bankGrantInitialLabels, hg]
        have hbad := hs.2.2 g g hh
        change False at hbad
        exact False.elim hbad
  · rintro ⟨hprotected, hfree⟩
    refine ⟨hprotected,
      bankGrantInitialLabeled_cover ring hbank s, ?_⟩
    intro i g hi
    have hfalse : s.grant i = false := hfree i
    simp [bankGrantInitialLabeledState, bankGrantInitialLabels,
      hfalse] at hi

theorem bankGrantInitial_not_marked_of_live {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (g : Fin n) (hg : s.grant g = true) :
    ¬ BankGrantMarkedProtectedDomain ring hbank
        (bankGrantInitialLabeledState ring hbank s) := by
  intro hmarked
  have hfree : GrantFree s :=
    (bankGrantInitial_marked_iff_grantFree ring hbank s).mp hmarked |>.2
  have hz : s.grant g = false := hfree g
  rw [hg] at hz
  cases hz

end L3.RenewalReferenceClock


/-!
Repair the initial-label carrier before the marked grant drain.

This section does not amend the
old all-marked domain, which is unusable with initial live grants.
The new geometry admits a live UNMARKED label. Its reserve is 3*n:
a nominal n-hit first-branch allowance plus a nominal 2*n
post-marking drain allowance. These are bookkeeping ceilings;
they are NOT yet a proven scalar drift bound for every unmarked
grant. The paper's first branch follows non-leftmost live BULLET
identities and proves a disjunction, not the assertion that every
unmarked GRANT individually retires after n hits.

In particular, the existing bankGrantLabelAdvance preserves a
label's mark field. Thus the source implementation still lacks
the mark-upgrade and bullet-identity/noncrossing simulation needed
for an unconditional nominated quota decrease. The initial
ledger is nevertheless now inside the new domain, and the source
and responder token owners can be audited separately for cover.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Extend the earlier geometry to live, initially unmarked grants.
For an unmarked label, a proof of noncrossing with a tracked
non-leftmost bullet is a future stage condition, not a premise
of this initialization domain. Marked strong quotas are capped
by n and weak quotas by 2*n. -/
def BankGrantLabelGeometryAll {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) : Prop :=
  ∀ (i : Fin n) (g : Fin n),
    (s.labels i).host = some g →
      match (s.labels i).mark with
      | .unmarked => True
      | .terminal => s.physical.request g = true
      | .strong =>
          0 < (s.labels i).remaining ∧
          (s.labels i).remaining ≤ n ∧
          grantDrainLeftLeaderDistance ring s.physical.native g ≤
            (s.labels i).remaining ∧
          BankGrantStrongLock ring s.physical g
      | .weak =>
          0 < (s.labels i).remaining ∧
          (s.labels i).remaining ≤ 2 * n ∧
          (BankGrantWeakLock ring s.physical g ∨
            BankGrantStrongLock ring s.physical g)

/-- Repaired carrier: same actual protected BANK physical projection
and the exact no-cloning cover, but does not require all labels to
have entered a marked lock or terminal condition. -/
def BankGrantProtectedDomainAll {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank) : Prop :=
  BankExtinctDrainProtectedDomain ring hbank s.physical ∧
  BankGrantLabeledCover s ∧
  BankGrantLabelGeometryAll s

/-- Non-vacuity at the intended entry point: for EVERY protected
projected drain cut, including one with live grants, the original
initial label ledger is in the repaired domain. No artificial
proof of physical PPlus or authority extinction is assumed. -/
theorem bankGrantInitial_in_domainAll {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (hprotected : BankExtinctDrainProtectedDomain ring hbank s) :
    BankGrantProtectedDomainAll ring hbank
      (bankGrantInitialLabeledState ring hbank s) := by
  refine ⟨hprotected, bankGrantInitialLabeled_cover ring hbank s, ?_⟩
  intro i g _
  change True
  exact True.intro

/-- The scalar reserve associated with an initial, unmarked GRANT
has two parts: n for the first collective comparison and 2*n
for a subsequent weak-marked drain. This is not a claim of
monotonicity under the current ghost update. -/
def bankGrantLabelQuotaAll {n : Nat} (label : BankGrantLabel n) : Nat :=
  match label.host with
  | none => 0
  | some _ =>
      match label.mark with
      | .unmarked => 3 * n
      | .terminal => 1
      | .strong | .weak => label.remaining

def bankGrantQuotaAll {n : Nat} {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantLabeledState ring hbank) (i : Fin n) : Nat :=
  bankGrantLabelQuotaAll (s.labels i)

theorem bankGrantInitial_quotaAll {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (i : Fin n) :
    bankGrantQuotaAll (bankGrantInitialLabeledState ring hbank s) i =
      if s.grant i then 3 * n else 0 := by
  cases hg : s.grant i with
  | true =>
      simp [bankGrantQuotaAll, bankGrantLabelQuotaAll,
        bankGrantInitialLabeledState, bankGrantInitialLabels, hg]
  | false =>
      simp [bankGrantQuotaAll, bankGrantLabelQuotaAll,
        bankGrantInitialLabeledState, bankGrantInitialLabels, hg]

/-- Uniform numerical cap for the accounting reserve. GeometryAll
imposes the strong/weak caps, and a live Fin n host implies n>0. -/
theorem bankGrantQuotaAll_le_three {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (hgeo : BankGrantLabelGeometryAll s)
    (i : Fin n) :
    bankGrantQuotaAll s i ≤ 3 * n := by
  cases hh : (s.labels i).host with
  | none =>
      simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh]
  | some g =>
      have hg := hgeo i g hh
      have hn : 0 < n := by
        have hlt := g.isLt
        omega
      cases hm : (s.labels i).mark with
      | unmarked =>
          simp only [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          exact Nat.le_refl _
      | terminal =>
          simp only [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega
      | strong =>
          simp only [hm] at hg
          have hb : (s.labels i).remaining ≤ n := hg.2.1
          simp only [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega
      | weak =>
          simp only [hm] at hg
          have hb : (s.labels i).remaining ≤ 2 * n := hg.2.1
          simp only [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega

/-- The hzero implication is restored for live unmarked labels:
their 3*n quota is positive, whereas a retired label has zero.
The cover hypothesis is essential. -/
theorem bankGrantQuotaAll_zero_implies_GrantFree {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (hs : BankGrantProtectedDomainAll ring hbank s)
    (hz : ∀ i : Fin n, bankGrantQuotaAll s i = 0) :
    GrantFree s.physical := by
  intro g
  cases hgrant : s.physical.grant g with
  | false =>
      rfl
  | true =>
      obtain ⟨i, hh⟩ := (hs.2.1 g).mp hgrant
      have hg := hs.2.2 i g hh
      have hzero : bankGrantQuotaAll s i = 0 := hz i
      have hn : 0 < n := by
        have hlt := g.isLt
        omega
      cases hm : (s.labels i).mark with
      | unmarked =>
          have hq : bankGrantQuotaAll s i = 3 * n := by
            simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega
      | terminal =>
          have hq : bankGrantQuotaAll s i = 1 := by
            simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega
      | strong =>
          simp only [hm] at hg
          have hp : 0 < (s.labels i).remaining := hg.1
          have hq : bankGrantQuotaAll s i =
              (s.labels i).remaining := by
            simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega
      | weak =>
          simp only [hm] at hg
          have hp : 0 < (s.labels i).remaining := hg.1
          have hq : bankGrantQuotaAll s i =
              (s.labels i).remaining := by
            simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hh, hm]
          omega

/-- Important limitation: the *existing* ghost step cannot mark an
unmarked label. This holds on every edge, even when the host moves
or coalesces with another label. -/
theorem bankGrantFamilyNext_preserves_unmarked {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (i e : Fin n)
    (hm : (s.labels i).mark = BankGrantMark.unmarked) :
    ((bankGrantFamilyNext ring hbank s e).labels i).mark =
      BankGrantMark.unmarked := by
  change (s.labels i).mark = BankGrantMark.unmarked
  exact hm

/-- As long as an unmarked label still has a host, its current
3*n reserve remains CONSTANT under the update. Therefore
a strict nominated-edge decrease for this reserve would be false
without adding an actual marking / noncrossing ghost step. -/
theorem bankGrantUnmarked_survivor_quota_constant {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantLabeledState ring hbank)
    (i e g : Fin n)
    (hm : (s.labels i).mark = BankGrantMark.unmarked)
    (hhost :
      ((bankGrantFamilyNext ring hbank s e).labels i).host = some g) :
    bankGrantQuotaAll (bankGrantFamilyNext ring hbank s e) i =
      3 * n := by
  have hmark := bankGrantFamilyNext_preserves_unmarked
    ring hbank s i e hm
  simp [bankGrantQuotaAll, bankGrantLabelQuotaAll, hhost, hmark]

/-- The remaining first-branch proof is about tracked non-leftmost
live BULLET identities and their opposite-direction noncrossing
with an unmarked grant. It must certify a transition into a
marked/candidate sector; only then is a per-grant 2*n drain quota
justified. The current proof-only state does not store that bullet
identity, so no such transition or strict drop is asserted here. -/
def BankGrantUnmarkedNoncrossingPending {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (s : BankGrantLabeledState ring hbank),
    BankGrantProtectedDomainAll ring hbank s →
    ¬ GrantFree s.physical →
    (∀ i : Fin n,
      (s.labels i).host ≠ none →
      (s.labels i).mark = .unmarked →
      bankGrantQuotaAll s i = 3 * n)

end L3.RenewalReferenceClock


/-!
Two distinct families of proof-only identities.

A non-leftmost live bullet is tracked
by its INITIAL site (Fin n); the original grant identities remain
the other Fin n family. Retired identities retain their index but
have no host.

IMPORTANT MATHEMATICAL SCOPE: the paper's first collective branch
charges nominated hits of surviving non-leftmost bullets against
the existence of an UNMARKED grant. It does not give an independent
strictly decreasing bullet rank on every edge, nor a globally
decreasing 3*n rank for each unmarked grant. The meaningful clock
is the clockwise bullet-to-grant separation, indexed by a PAIR.
It is < n, but its decrease requires the outstanding noncrossing
and ghost-transport proof.

For this reason the correct tail interface below is a cross-charge
word inclusion, not the all-label hdrop premise of
grantQuota_family_survival_half. The combinatorial lower-tail
conversion itself is fully generic and needs no independence
between bullet identities.

All source and protocol definitions above are unchanged.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A live follower bullet is non-leftmost if some OTHER live
follower bullet lies earlier in the same sector. Both are located
using the real native leader-sector relation. This is a
proof observer, not a new physical field. -/
def BankGrantNonleftmostLive {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n) : Prop :=
  L3.LiveBullet N b ∧ (N b).l = false ∧
  ∃ (p a : Fin n),
    L3.leaderSector ring N p b ∧
    L3.leaderSector ring N p a ∧
    L3.LiveBullet N a ∧
    (N a).l = false ∧
    PPL.cyclicOffset ring p a < PPL.cyclicOffset ring p b

/-- One initial non-leftmost live bullet identity; the optional
partner is only a proposed witness for a pair-separation observer.
It is NOT a certificate of global bullet ancestry. -/
structure BankGrantBulletIdentity (n : Nat) where
  host : Option (Fin n)
  partner : Option (Fin n)

/-- At most one initially tracked bullet identity per physical site.
The optional partner is one existing grant site when such a site
exists, without asserting any noncrossing condition. -/
private noncomputable def bankGrantInitialPartner {n : Nat}
    {Scratch : Type} (s : GrantDrainState n Scratch) :
    Option (Fin n) := by
  classical
  exact if h : ∃ i : Fin n, s.grant i = true
    then some (Classical.choose h) else none

noncomputable def bankGrantInitialBulletIdentity {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch)
    (j : Fin n) : BankGrantBulletIdentity n := by
  classical
  exact {
    host :=
      if BankGrantNonleftmostLive ring s.native j
      then some j else none
    partner := bankGrantInitialPartner s
  }

/-- Two disjoint identity namespaces: n possible initial grants
and n possible initial non-leftmost live bullets. The number of
ACTIVE bullet identities is at most n, with no dynamically created
identity. It is intentional that this state has no invented
bullet transition rule yet. -/
structure BankGrantDualState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) where
  grants : BankGrantLabeledState ring hbank
  bullets : Fin n → BankGrantBulletIdentity n

/-- Exact initial ghost extension of the actual projected drain. -/
noncomputable def bankGrantInitialDualState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank)) :
    BankGrantDualState ring hbank :=
  { grants := bankGrantInitialLabeledState ring hbank s
    bullets := bankGrantInitialBulletIdentity ring s }

/-- The restored physical/label carrier together with a bullet
identity *snapshot* obligation. Closure and actual bullet transport
are separate proof obligations, not hidden inside this definition. -/
def BankGrantDualDomain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) : Prop :=
  BankGrantProtectedDomainAll ring hbank s.grants ∧
  ∀ (j b : Fin n),
    (s.bullets j).host = some b →
      BankGrantNonleftmostLive ring s.grants.physical.native b

/-- Initial non-vacuity: every protected projected BANK cut
(including ones carrying arbitrary initial grants) extends to
this two-family domain. No mark or bullet identity is assumed to
have been retired beforehand. -/
theorem bankGrantInitialDual_in_domain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (hs : BankExtinctDrainProtectedDomain ring hbank s) :
    BankGrantDualDomain ring hbank
      (bankGrantInitialDualState ring hbank s) := by
  classical
  refine ⟨bankGrantInitial_in_domainAll ring hbank s hs, ?_⟩
  intro j b hhost
  change
    (if BankGrantNonleftmostLive ring s.native j then some j else none) =
      some b at hhost
  change BankGrantNonleftmostLive ring s.native b
  by_cases hj : BankGrantNonleftmostLive ring s.native j
  · have he : (some j : Option (Fin n)) = some b := by
      simpa only [if_pos hj] using hhost
    have hsame : j = b := Option.some.inj he
    rw [← hsame]
    exact hj
  · have he : (none : Option (Fin n)) = some b := by
      simpa only [if_neg hj] using hhost
    cases he

/-- A fixed Fin n index exists for every possible initial bullet
identity, so even without injective host transport there can never
be more than n live *identities*. -/
theorem bankGrantBullet_identity_count_le {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) :
    (List.ofFn (fun j : Fin n =>
      if (s.bullets j).host.isSome then 1 else 0)).sum ≤ n := by
  calc
    _ ≤ (List.ofFn (fun _ : Fin n => 1)).sum :=
      ofFn_sum_le _ _ (fun j => by
        cases h : (s.bullets j).host <;> simp [h])
    _ = n := by
      rw [ofFn_sum_const]
      omega

/-- A bullet's nominated hit is its outgoing physical edge,
before the random scheduler symbol is drawn. A retired bullet
still nominates its immutable initial index, as required by
the lower-tail word lemma. -/
def bankGrantBulletChosen {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantDualState ring hbank) (j : Fin n) : Fin n :=
  match (s.bullets j).host with
  | none => j
  | some b => b

/-- The clockwise separation from the bullet host b to its
partner grant host g. The partner may cease to exist, so this
becomes zero; it is not an independent, continuously decreasing
bullet rank. This is the correct n-bounded pair observer in the
paper's opposite-direction noncrossing argument. -/
def bankGrantBulletPairQuota {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantDualState ring hbank) (j : Fin n) : Nat :=
  match (s.bullets j).host, (s.bullets j).partner with
  | some b, some i =>
      match (s.grants.labels i).host with
      | some g => PPL.cyclicOffset ring b g
      | none => 0
  | _, _ => 0

/-- Every clockwise pair separation is strictly below one full
ring, regardless of whether the labels are successfully coupled.
Positive separation for an actually live unmarked/bullet pair
is a further peacefulness/noncrossing fact, not used here. -/
theorem bankGrantBulletPairQuota_lt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (j : Fin n) :
    bankGrantBulletPairQuota s j < n := by
  cases hb : (s.bullets j).host with
  | none =>
      simp [bankGrantBulletPairQuota, hb, ring.hn]
  | some b =>
      cases hp : (s.bullets j).partner with
      | none =>
          simp [bankGrantBulletPairQuota, hb, hp, ring.hn]
      | some i =>
          cases hg : (s.grants.labels i).host with
          | none =>
              simp [bankGrantBulletPairQuota, hb, hp, hg, ring.hn]
          | some g =>
              have ht : PPL.cyclicOffset ring b g < n := by
                unfold PPL.cyclicOffset
                exact Nat.mod_lt _ ring.hn
              simpa only [bankGrantBulletPairQuota, hb, hp, hg] using ht

/-- The joint index has two constructors, so a grant identity
and a bullet identity can never be confused even after coalescence. -/
def bankGrantDualChosen {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantDualState ring hbank) :
    Sum (Fin n) (Fin n) → Fin n
  | .inl i => bankGrantChosen s.grants i
  | .inr j => bankGrantBulletChosen s j

/-- This is a storage quota, NOT a uniform hdrop certificate.
For unmarked grant labels the previously quotaAll reserves
3*n. For bullet labels we use the explicitly paired clockwise
separation (<n), not an invented independent retirement clock. -/
def bankGrantDualQuota {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantDualState ring hbank) :
    Sum (Fin n) (Fin n) → Nat
  | .inl i => bankGrantQuotaAll s.grants i
  | .inr j => bankGrantBulletPairQuota s j

theorem bankGrantDual_initial_grant_quota {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : GrantDrainState n (BankReferenceState ring hbank))
    (i : Fin n) :
    bankGrantDualQuota (bankGrantInitialDualState ring hbank s)
      (.inl i) =
    if s.grant i then 3 * n else 0 := by
  exact bankGrantInitial_quotaAll ring hbank s i

/-- hzero is inherited through the GRANT half of the joint family.
It does not depend on any unproved noncrossing transition. -/
theorem bankGrantDual_zero_implies_GrantFree {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank)
    (hs : BankGrantDualDomain ring hbank s)
    (hz : ∀ i : Sum (Fin n) (Fin n),
      bankGrantDualQuota s i = 0) :
    GrantFree s.grants.physical := by
  apply bankGrantQuotaAll_zero_implies_GrantFree
    ring hbank s.grants hs.1
  intro i
  exact hz (.inl i)

/-- The first stage ends when every surviving grant is marked OR
all tracked initial non-leftmost live bullet identities have retired.
Only the conjunction of those failure events is charged to the
nominated hits of BULLET identities. -/
def BankGrantFirstStageDone {n : Nat}
    {ring : DirectedRing n}
    {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (s : BankGrantDualState ring hbank) : Prop :=
  (∀ i : Fin n, (s.grants.labels i).host ≠ none →
    (s.grants.labels i).mark ≠ BankGrantMark.unmarked) ∨
  (∀ j : Fin n, (s.bullets j).host = none)

/-- The missing machine-specific spatial proof, stated as a
*cross-charge* inclusion of every still-surviving word in a union
of short-hit BULLET identities. It has no separate grant hdrop
premise. Proving it requires: (i) bullet ancestry through native E
and births, (ii) no creation of non-leftmost identities,
(iii) opposite-direction noncrossing, and (iv) mark promotion.
It is not asserted for the present ghost update. -/
def BankGrantBulletCrossChargeOn {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (chosen : Fin d → S → Fin n) (Q : Nat) : Prop :=
  ∀ (x : S), I x → ∀ (w : List (Fin n)),
    UniformFirstHit.survivalWord next P x w = 1 →
      ∃ j : Fin d, grantQuotaHits next (chosen j) x w < Q

/-- The first-branch analogue of quota-to-hitting. The physical
cross-charge proof supplies the one semantic hypothesis above;
the rest is the exact nominated lower-tail inequality.
The d bullet identities can be correlated arbitrarily. -/
theorem bankGrantBullet_cross_charge_mass
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (chosen : Fin d → S → Fin n)
    (Q T : Nat)
    (hn : 0 < n)
    (hT : 2 * n * Q + n ≤ T)
    (hcross : BankGrantBulletCrossChargeOn next I P chosen Q)
    (x : S) (hx : I x) :
    2 * UniformFirstHit.survivalNumerator next P x T ≤
      d * n ^ T := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord next P x w ≤
        (if (List.ofFn (fun j : Fin d =>
            decide (grantQuotaHits next (chosen j) x w < Q))).any
              (fun z => z)
         then 1 else 0) := by
    by_cases hs :
        UniformFirstHit.survivalWord next P x w = 1
    · obtain ⟨j, hj⟩ := hcross x hx w hs
      have hany :
          (List.ofFn (fun i : Fin d =>
            decide (grantQuotaHits next (chosen i) x w < Q))).any
              (fun z => z) = true := by
        rw [List.any_eq_true]
        exact ⟨true, List.mem_ofFn.mpr ⟨j, by simp [hj]⟩, rfl⟩
      simp [hs, hany]
    · have hz :
          UniformFirstHit.survivalWord next P x w = 0 := by
        have hb := grantQuotaSurvivalBit next P x w
        omega
      simp [hz]
  have hmass :
      UniformFirstHit.survivalNumerator next P x T ≤
        L3.Prob.scheduleSum n T
          (fun w =>
            if (List.ofFn (fun j : Fin d =>
              decide (grantQuotaHits next (chosen j) x w < Q))).any
                (fun z => z)
            then 1 else 0) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord next P x) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  calc
    2 * UniformFirstHit.survivalNumerator next P x T ≤
        2 * L3.Prob.scheduleSum n T
          (fun w =>
            if (List.ofFn (fun j : Fin d =>
              decide (grantQuotaHits next (chosen j) x w < Q))).any
                (fun z => z)
            then 1 else 0) := Nat.mul_le_mul_left _ hmass
    _ = L3.Prob.scheduleSum n T
          (fun w =>
            if (List.ofFn (fun j : Fin d =>
              decide (grantQuotaHits next (chosen j) x w < Q))).any
                (fun z => z)
            then 1 else 0) * 2 := Nat.mul_comm _ _
    _ ≤ d * n ^ T := by
      exact nominatedHits_family_lower_tail_half next chosen
        (fun j => grantQuotaHits next (chosen j))
        (by intro j y; rfl)
        (by intro j y e es; rfl)
        x T Q hn hT

end L3.RenewalReferenceClock


/-!
Repair the cross-charge union bound and install an explicit
initial-bullet ancestry transport interface.

The first theorem below is the NONVACUOUS
weighted lower-tail bound: 2 * survival <= n^T, NOT d*n^T.

The source BankGrantDualState has only a snapshot of the initial
non-leftmost live bullets; it has no successor operation for that
snapshot. The proof-only successor defined below is tied to the
ACTUAL bankGrantFamilyNext physical step. It never revives a retired
identity and permits only rightward movement, staying at the old
site, or retirement. Survival is checked against the new native
non-leftmost-live predicate, so this is a conservative observer.

Faithful completeness of the ancestry (that the ghost does not
retire a still-non-leftmost original bullet) and the physical
no-new-non-leftmost-IDENTITY theorem require the missing sector
proof. Structural no-creation of ghost identities alone is not
that missing physical theorem. The concrete native row at the
end shows why freezing the old host would be incorrect.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A surviving first-branch word forces a short-hit bullet
identity.  The wordwise cross-charge premise is exactly the one
used earlier. Padding the horizon by d decay blocks removes
the previously vacuous factor d in the union bound. -/
theorem bankGrantBullet_cross_charge_half
    {S : Type} {n d : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (chosen : Fin d → S → Fin n)
    (Q T : Nat)
    (hn : 0 < n)
    (hT : 2 * n * (Q + d) + n ≤ T)
    (hcross : BankGrantBulletCrossChargeOn next I P chosen Q)
    (x : S) (hx : I x) :
    2 * UniformFirstHit.survivalNumerator next P x T ≤
      n ^ T := by
  classical
  have hpoint (w : List (Fin n)) :
      UniformFirstHit.survivalWord next P x w ≤
      (List.ofFn (fun j : Fin d =>
        if grantQuotaHits next (chosen j) x w < Q then 1 else 0)).sum := by
    calc
      _ ≤ (if (List.ofFn (fun j : Fin d =>
            decide (grantQuotaHits next (chosen j) x w < Q))).any
              (fun z => z)
          then 1 else 0) := by
        by_cases hs :
            UniformFirstHit.survivalWord next P x w = 1
        · obtain ⟨j, hj⟩ := hcross x hx w hs
          have hany :
              (List.ofFn (fun i : Fin d =>
                decide (grantQuotaHits next (chosen i) x w < Q))).any
                  (fun z => z) = true := by
            rw [List.any_eq_true]
            exact ⟨true, List.mem_ofFn.mpr ⟨j, by simp [hj]⟩, rfl⟩
          simp [hs, hany]
        · have hz :
              UniformFirstHit.survivalWord next P x w = 0 := by
            have hb := grantQuotaSurvivalBit next P x w
            omega
          simp [hz]
      _ ≤ (List.ofFn (fun j : Fin d =>
            if decide (grantQuotaHits next (chosen j) x w < Q)
            then 1 else 0)).sum :=
        grantTailFamilyIndicator d
          (fun j : Fin d =>
            decide (grantQuotaHits next (chosen j) x w < Q))
      _ = (List.ofFn (fun j : Fin d =>
            if grantQuotaHits next (chosen j) x w < Q then 1 else 0)).sum := by
        apply ofFn_sum_eq
        intro j
        by_cases hj : grantQuotaHits next (chosen j) x w < Q
        · simp [hj]
        · simp [hj]
  have hmass :
      UniformFirstHit.survivalNumerator next P x T ≤
      L3.Prob.scheduleSum n T
        (fun w => (List.ofFn (fun j : Fin d =>
          if grantQuotaHits next (chosen j) x w < Q
          then 1 else 0)).sum) := by
    change L3.Prob.scheduleSum n T
      (UniformFirstHit.survivalWord next P x) ≤ _
    exact L3.Density.schedule_sum_mono T _ _ hpoint
  have hrow (j : Fin d) :
      2 ^ (T + 1) *
        L3.Prob.scheduleSum n T
          (fun w =>
            if grantQuotaHits next (chosen j) x w < Q then 1 else 0) ≤
      2 ^ Q * (2 * n - 1) ^ T :=
    grantTailWeighted next (chosen j)
      (grantQuotaHits next (chosen j))
      (by intro y; rfl)
      (by intro y e es; rfl) x T Q hn
  have hweighted :
      2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator next P x T ≤
      d * (2 ^ Q * (2 * n - 1) ^ T) := by
    calc
      _ ≤ 2 ^ (T + 1) *
            L3.Prob.scheduleSum n T
              (fun w => (List.ofFn (fun j : Fin d =>
                if grantQuotaHits next (chosen j) x w < Q
                then 1 else 0)).sum) :=
          Nat.mul_le_mul_left _ hmass
      _ = (List.ofFn (fun j : Fin d =>
            2 ^ (T + 1) *
              L3.Prob.scheduleSum n T
                (fun w =>
                  if grantQuotaHits next (chosen j) x w < Q
                  then 1 else 0))).sum := by
          rw [L3.Density.schedule_sum_fin, ← ofFn_sum_mul_left]
      _ ≤ (List.ofFn (fun _ : Fin d =>
            2 ^ Q * (2 * n - 1) ^ T)).sum :=
          ofFn_sum_le _ _ hrow
      _ = d * (2 ^ Q * (2 * n - 1) ^ T) :=
          ofFn_sum_const _ _
  have hcoef :
      d * (2 ^ Q * (2 * n - 1) ^ T) ≤
      2 ^ (Q + d) * (2 * n - 1) ^ T := by
    calc
      _ = (d * 2 ^ Q) * (2 * n - 1) ^ T := by ac_rfl
      _ ≤ (2 ^ d * 2 ^ Q) * (2 * n - 1) ^ T :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (grantQuotaLabelLePow d))
      _ = 2 ^ (Q + d) * (2 * n - 1) ^ T := by
        rw [Nat.pow_add]
        ac_rfl
  have hdecay :
      2 ^ (Q + d) * (2 * n - 1) ^ T ≤ (2 * n) ^ T :=
    grantTailDecay n T (Q + d) hn (by omega)
  have hfinal :
      2 ^ (T + 1) *
        UniformFirstHit.survivalNumerator next P x T ≤ (2 * n) ^ T :=
    Nat.le_trans (Nat.le_trans hweighted hcoef) hdecay
  have hscaled :
      2 ^ T *
        (2 * UniformFirstHit.survivalNumerator next P x T) ≤
      2 ^ T * n ^ T := by
    calc
      _ = 2 ^ (T + 1) *
            UniformFirstHit.survivalNumerator next P x T := by
          rw [Nat.pow_succ]
          ac_rfl
      _ ≤ (2 * n) ^ T := hfinal
      _ = 2 ^ T * n ^ T := by
          rw [Nat.mul_pow]
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < (2 : Nat)))

/-- The new native field is the actual adapted projected no-producer
BANK reference successor; the bullet observer sees this, not a
hypothetical pure E-only machine. -/
private def bankGrantBulletNextNative {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e : Fin n) :
    Fin n → CertNative :=
  (bankGrantFamilyNext ring hbank s.grants e).physical.native

/-- A source bullet can be transported right only if it was a
live follower, the old responder was an empty follower, and the
new responder is still a NON-LEFTMOST live bullet. -/
private def bankGrantBulletSourceMoveValid {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e : Fin n) : Prop :=
  L3.LiveBullet s.grants.physical.native e ∧
  (s.grants.physical.native e).l = false ∧
  (s.grants.physical.native (ring.rightNeighbor e)).l = false ∧
  (s.grants.physical.native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
  BankGrantNonleftmostLive ring
    (bankGrantBulletNextNative ring hbank s e) (ring.rightNeighbor e)

/-- Conservative proof-only transport for an INITIAL tracked bullet:
the source site may send it to the responder; at any other site it
may remain there. Otherwise the proof identity is retired. No
new physical token or new identity is ever created here. -/
private noncomputable def bankGrantBulletTransport {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j : Fin n) :
    Option (Fin n) := by
  classical
  exact
    match (s.bullets j).host with
    | none => none
    | some b =>
        if b = e then
          if bankGrantBulletSourceMoveValid ring hbank s e then
            some (ring.rightNeighbor e)
          else none
        else if BankGrantNonleftmostLive ring
            (bankGrantBulletNextNative ring hbank s e) b then
          some b
        else none

/-- This successor is genuinely tied to bankGrantFamilyNext on the
physical/reference coordinate. The bullet fields are a proposed
conservative ghost transport, not protocol state. -/
noncomputable def bankGrantDualNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e : Fin n) :
    BankGrantDualState ring hbank :=
  { grants := bankGrantFamilyNext ring hbank s.grants e
    bullets := fun j =>
      { s.bullets j with host := bankGrantBulletTransport ring hbank s e j } }

theorem bankGrantDualNext_physical {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e : Fin n) :
    (bankGrantDualNext ring hbank s e).grants.physical =
      grantDrainStep ring
        (bankStageDrainFresh ring hbank)
        (bankStageDrainScratchNext ring hbank)
        s.grants.physical e := by
  rfl

/-- No retired initial bullet identity can be reactivated by one
actual projected reference step under the new ghost transport. -/
theorem bankGrantDualNext_no_new_bullet_identity {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j : Fin n)
    (hretired : (s.bullets j).host = none) :
    ((bankGrantDualNext ring hbank s e).bullets j).host = none := by
  change bankGrantBulletTransport ring hbank s e j = none
  simp [bankGrantBulletTransport, hretired]

/-- Exact structural alternatives: one initial bullet identity
either retires, stays at its old site, or moves right on the
actually selected outgoing edge. In particular this never invents
a third site and never resurrects an initially retired identity. -/
theorem bankGrantDualNext_transport_or_retire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j : Fin n) :
    ((bankGrantDualNext ring hbank s e).bullets j).host = none ∨
    ∃ b : Fin n, (s.bullets j).host = some b ∧
      (((bankGrantDualNext ring hbank s e).bullets j).host = some b ∨
        (b = e ∧
          ((bankGrantDualNext ring hbank s e).bullets j).host =
            some (ring.rightNeighbor e))) := by
  classical
  cases hhost : (s.bullets j).host with
  | none =>
      left
      change bankGrantBulletTransport ring hbank s e j = none
      simp [bankGrantBulletTransport, hhost]
  | some b =>
      by_cases hb : b = e
      · by_cases hmove : bankGrantBulletSourceMoveValid ring hbank s e
        · right
          refine ⟨b, rfl, Or.inr ⟨hb, ?_⟩⟩
          change bankGrantBulletTransport ring hbank s e j =
            some (ring.rightNeighbor e)
          simp [bankGrantBulletTransport, hhost, hb, hmove]
        · left
          change bankGrantBulletTransport ring hbank s e j = none
          simp [bankGrantBulletTransport, hhost, hb, hmove]
      · by_cases hstay : BankGrantNonleftmostLive ring
            (bankGrantBulletNextNative ring hbank s e) b
        · right
          refine ⟨b, rfl, Or.inl ?_⟩
          change bankGrantBulletTransport ring hbank s e j = some b
          simp [bankGrantBulletTransport, hhost, hb, hstay]
        · left
          change bankGrantBulletTransport ring hbank s e j = none
          simp [bankGrantBulletTransport, hhost, hb, hstay]

/-- Every ghost identity which survives the conservative update is
a real non-leftmost LIVE bullet at its claimed NEW physical site.
The reverse direction needs the native sector/noncrossing proof. -/
theorem bankGrantDualNext_survivor_native {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j b : Fin n)
    (hsurvives :
      ((bankGrantDualNext ring hbank s e).bullets j).host = some b) :
    BankGrantNonleftmostLive ring
      (bankGrantDualNext ring hbank s e).grants.physical.native b := by
  classical
  have hh : bankGrantBulletTransport ring hbank s e j = some b := by
    exact hsurvives
  cases hhost : (s.bullets j).host with
  | none =>
      simp [bankGrantBulletTransport, hhost] at hh
  | some c =>
      by_cases hc : c = e
      · by_cases hmove : bankGrantBulletSourceMoveValid ring hbank s e
        · have he :
              (some (ring.rightNeighbor e) : Option (Fin n)) = some b := by
            simpa [bankGrantBulletTransport, hhost, hc, hmove] using hh
          have hbe : ring.rightNeighbor e = b := Option.some.inj he
          change BankGrantNonleftmostLive ring
            (bankGrantBulletNextNative ring hbank s e) b
          rw [← hbe]
          exact hmove.2.2.2.2
        · simp [bankGrantBulletTransport, hhost, hc, hmove] at hh
      · by_cases hstay : BankGrantNonleftmostLive ring
            (bankGrantBulletNextNative ring hbank s e) c
        · have he : (some c : Option (Fin n)) = some b := by
            simpa [bankGrantBulletTransport, hhost, hc, hstay] using hh
          have hbe : c = b := Option.some.inj he
          change BankGrantNonleftmostLive ring
            (bankGrantBulletNextNative ring hbank s e) b
          rw [← hbe]
          exact hstay
        · simp [bankGrantBulletTransport, hhost, hc, hstay] at hh

/-- Actual new bullet snapshots satisfy the bullet half of the
dual domain. This does NOT assert grant-cover or quota closure. -/
theorem bankGrantDualNext_bullet_domain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e : Fin n) :
    ∀ j b : Fin n,
      ((bankGrantDualNext ring hbank s e).bullets j).host = some b →
      BankGrantNonleftmostLive ring
        (bankGrantDualNext ring hbank s e).grants.physical.native b := by
  intro j b hs
  exact bankGrantDualNext_survivor_native ring hbank s e j b hs

/-! A concrete row showing that keeping a bullet label at its old
site (as a frozen snapshot) is NOT a faithful identity transport. -/

private def bankGrantBulletRowOldSource : CertNative :=
  { l := false, b := (2 : Fin 3), sh := true, sg := false }

private def bankGrantBulletRowOldResponder : CertNative :=
  { l := false, b := (0 : Fin 3), sh := false, sg := false }

/-- On a follower-source live-bullet / empty-follower interaction,
native E sends the source bullet clockwise from X to Y.
At X the old bullet disappears, while Y receives live value 2. -/
theorem bankGrantBullet_concrete_move_row :
    (certLiteralEPair bankGrantBulletRowOldSource
      bankGrantBulletRowOldResponder).1.b = (0 : Fin 3) ∧
    (certLiteralEPair bankGrantBulletRowOldSource
      bankGrantBulletRowOldResponder).2.b = (2 : Fin 3) := by
  simp [bankGrantBulletRowOldSource, bankGrantBulletRowOldResponder,
    certLiteralEPair, certFinThree]

/-- Ring shape: leader at 0; initial live bullets at 1 and 2;
site 3 is an empty follower; the nominated outgoing edge is
2 -> 3. This describes the local motion shape, not a verified
inhabitant of BankExtinctDrainProtectedDomain. -/
private def bankGrantBulletExampleRing : DirectedRing 5 := ⟨by decide⟩

private def bankGrantBulletExampleNative (i : Fin 5) : CertNative :=
  if i = (0 : Fin 5) then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i = (1 : Fin 5) then
    { l := false, b := (2 : Fin 3), sh := true, sg := false }
  else if i = (2 : Fin 5) then
    bankGrantBulletRowOldSource
  else
    bankGrantBulletRowOldResponder

/-- The native step really moves the bullet to site 3.
It disproves a frozen-location ghost update, but is NOT a
counterexample to the paper's no-new-non-leftmost-identity claim. -/
theorem bankGrantBullet_concrete_ring_move :
    (nativeE bankGrantBulletExampleRing bankGrantBulletExampleNative
      (2 : Fin 5) (2 : Fin 5)).b = (0 : Fin 3) ∧
    (nativeE bankGrantBulletExampleRing bankGrantBulletExampleNative
      (2 : Fin 5) (3 : Fin 5)).b = (2 : Fin 3) := by
  unfold bankGrantBulletExampleRing bankGrantBulletExampleNative
    bankGrantBulletRowOldSource bankGrantBulletRowOldResponder
    nativeE certLiteralEPair certFinThree
  decide

end L3.RenewalReferenceClock

/-!
The current R8 dual ghost freezes grant marks.
No unconditional BankGrantBulletCrossChargeOn is asserted.
The terminal HOLD counterrow is isolated below.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The only writes in the grant observer are host and remaining.
A marked grant cannot lose its mark, but an unmarked grant
also cannot become marked with the current successor. -/
theorem bankGrantDualNext_mark_frozen {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e i : Fin n) :
    ((bankGrantDualNext ring hbank s e).grants.labels i).mark =
      (s.grants.labels i).mark := by
  change (bankGrantLabelAdvance ring s.grants.physical e
    (s.grants.labels i)).mark = (s.grants.labels i).mark
  rfl

theorem bankGrantDualNext_marked_stays_marked {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e i : Fin n)
    (hm : (s.grants.labels i).mark ≠ BankGrantMark.unmarked) :
    ((bankGrantDualNext ring hbank s e).grants.labels i).mark ≠
      BankGrantMark.unmarked := by
  rw [bankGrantDualNext_mark_frozen ring hbank s e i]
  exact hm

theorem bankGrantDualNext_unmarked_stays_unmarked {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e i : Fin n)
    (hm : (s.grants.labels i).mark = BankGrantMark.unmarked) :
    ((bankGrantDualNext ring hbank s e).grants.labels i).mark =
      BankGrantMark.unmarked := by
  rw [bankGrantDualNext_mark_frozen ring hbank s e i]
  exact hm

/-- Persistent for every scheduler word; thus the intended
strong/terminal label promotion cannot arise from the initial
unmarked dual labeling without changing its proof-only update. -/
theorem bankGrantDualRun_mark_frozen {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank)
    (word : List (Fin n)) (i : Fin n) :
    ((word.foldl (bankGrantDualNext ring hbank) s).grants.labels i).mark =
      (s.grants.labels i).mark := by
  induction word generalizing s with
  | nil =>
      rfl
  | cons e rest ih =>
      simpa only [List.foldl_cons] using
        (ih (bankGrantDualNext ring hbank s e)).trans
          (bankGrantDualNext_mark_frozen ring hbank s e i)

theorem bankGrantDualRun_initial_marks_unmarked {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (initial : GrantDrainState n (BankReferenceState ring hbank))
    (word : List (Fin n)) (i : Fin n) :
    ((word.foldl (bankGrantDualNext ring hbank)
      (bankGrantInitialDualState ring hbank initial)).grants.labels i).mark =
      BankGrantMark.unmarked := by
  have hinit :
      ((bankGrantInitialDualState ring hbank initial).grants.labels i).mark =
        BankGrantMark.unmarked := by
    rfl
  exact (bankGrantDualRun_mark_frozen ring hbank
    (bankGrantInitialDualState ring hbank initial) word i).trans hinit

/-- From the initialized ghost, the all-marked first-stage branch
is actually a grant-extinction branch. -/
theorem bankGrantFirstStageDone_initial_extinction_or_bullets {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (initial : GrantDrainState n (BankReferenceState ring hbank))
    (word : List (Fin n))
    (hdone : BankGrantFirstStageDone
      (word.foldl (bankGrantDualNext ring hbank)
        (bankGrantInitialDualState ring hbank initial))) :
    (∀ i : Fin n,
      ((word.foldl (bankGrantDualNext ring hbank)
        (bankGrantInitialDualState ring hbank initial)).grants.labels i).host =
          none) ∨
    (∀ j : Fin n,
      ((word.foldl (bankGrantDualNext ring hbank)
        (bankGrantInitialDualState ring hbank initial)).bullets j).host =
          none) := by
  rcases hdone with hall | hbullets
  · left
    intro i
    by_cases hnone :
        ((word.foldl (bankGrantDualNext ring hbank)
          (bankGrantInitialDualState ring hbank initial)).grants.labels i).host =
          none
    · exact hnone
    · exact False.elim ((hall i hnone)
        (bankGrantDualRun_initial_marks_unmarked
          ring hbank initial word i))
  · exact Or.inr hbullets

/-! The incoming nominated grant edge need not move the grant:
when the OLD responder is held (request && grant) but is not
F1 eligible, HOLD beats counterclockwise grant transport. -/

/-- Exact Boolean T0/T1/HOLD row: old source has no request/grant,
old responder has both. Both are final followers, no fresh
request and no FIRE. OLD responder grant and request survive. -/
theorem bankGrantIncomingHold_token_row :
    (grantDrainTokenRow false false true true
      false false false GrantDrainFire.none).1.grant = false ∧
    (grantDrainTokenRow false false true true
      false false false GrantDrainFire.none).2.grant = true ∧
    (grantDrainTokenRow false false true true
      false false false GrantDrainFire.none).2.req = true := by
  unfold grantDrainTokenRow
  decide

/-- An old selected bullet at its nominated outgoing source cannot
stutter while surviving: it moves right or retires. -/
theorem bankGrantDualNext_bullet_outgoing_moves_if_survives {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j b : Fin n)
    (hhost : (s.bullets j).host = some e)
    (hnext :
      ((bankGrantDualNext ring hbank s e).bullets j).host = some b) :
    b = ring.rightNeighbor e := by
  classical
  change bankGrantBulletTransport ring hbank s e j = some b at hnext
  by_cases hmove : bankGrantBulletSourceMoveValid ring hbank s e
  · have hh :
        (some (ring.rightNeighbor e) : Option (Fin n)) = some b := by
      simpa [bankGrantBulletTransport, hhost, hmove] using hnext
    exact (Option.some.inj hh).symm
  · have hh : (none : Option (Fin n)) = some b := by
      simpa [bankGrantBulletTransport, hhost, hmove] using hnext
    cases hh

/-- The partner grant identity is fixed by the old dual step. -/
theorem bankGrantDualNext_partner_frozen {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank) (e j : Fin n) :
    ((bankGrantDualNext ring hbank s e).bullets j).partner =
      (s.bullets j).partner := by
  rfl

/-- A surviving bullet and partner grant at exactly their old
hosts have the same cyclic separation. In particular an
incoming HOLD hit gives NO unit decrease when both persist. -/
theorem bankGrantDualNext_pair_stutter {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank)
    (e j i b g : Fin n)
    (hb : (s.bullets j).host = some b)
    (hpartner : (s.bullets j).partner = some i)
    (hg : (s.grants.labels i).host = some g)
    (hbnew :
      ((bankGrantDualNext ring hbank s e).bullets j).host = some b)
    (hgnew :
      ((bankGrantDualNext ring hbank s e).grants.labels i).host = some g) :
    bankGrantBulletPairQuota (bankGrantDualNext ring hbank s e) j =
      bankGrantBulletPairQuota s j := by
  have hpnew :
      ((bankGrantDualNext ring hbank s e).bullets j).partner =
        some i := by
    rw [bankGrantDualNext_partner_frozen ring hbank s e j]
    exact hpartner
  simp only [bankGrantBulletPairQuota,
    hbnew, hpnew, hgnew, hb, hpartner, hg]

theorem bankGrantIncomingHold_no_pair_drop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (s : BankGrantDualState ring hbank)
    (e j i b g : Fin n)
    (hincoming : e = ring.leftNeighbor g)
    (hhold : s.grants.physical.request g = true)
    (hb : (s.bullets j).host = some b)
    (hpartner : (s.bullets j).partner = some i)
    (hg : (s.grants.labels i).host = some g)
    (hbnew :
      ((bankGrantDualNext ring hbank s e).bullets j).host = some b)
    (hgnew :
      ((bankGrantDualNext ring hbank s e).grants.labels i).host = some g) :
    ¬ (bankGrantBulletPairQuota (bankGrantDualNext ring hbank s e) j +
        1 ≤ bankGrantBulletPairQuota s j) := by
  have hh := bankGrantDualNext_pair_stutter
    ring hbank s e j i b g hb hpartner hg hbnew hgnew
  rw [hh]
  omega

/-- Exactly one remaining HOLD-resolution interface for the
current mark-frozen ghost. This would rule out a surviving
held incoming unmarked grant paired with a surviving stationary
bullet, on the actual dual domain. The paper instead PROMOTES the
held survivor to terminal; the current successor cannot do so.
This Prop is not proved or assumed for cross-charge. -/
def BankGrantIncomingHeldResolutionOn {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (s : BankGrantDualState ring hbank)
    (e j i b g : Fin n),
    BankGrantDualDomain ring hbank s →
    ¬ BankGrantFirstStageDone s →
    (s.bullets j).host = some b →
    (s.bullets j).partner = some i →
    (s.grants.labels i).host = some g →
    (s.grants.labels i).mark = BankGrantMark.unmarked →
    e = ring.leftNeighbor g →
    s.grants.physical.request g = true →
    ((bankGrantDualNext ring hbank s e).bullets j).host = none ∨
    ((bankGrantDualNext ring hbank s e).grants.labels i).host = none

end L3.RenewalReferenceClock
