import Leader.L3.NativeBirth

namespace L3

set_option autoImplicit false

/-!
Candidate-owner extraction and genuinely generated ghost histories.

H_cand is the Phi-word class of
repair.tex (PAPER-UPDATES 21:15; definition author-only). The two closure invariants
(native 0*1* sector, single bullet; first credit genuine and retired) are NOT proved here.

An "incoming first-entry witness" stores the actual OLD source and
destination snapshots from the service that selected DP1.  The literal
ENTER flag is an incoming attempt on arbitrary Cartesian states:
a source bullet can collide with a pre-existing destination bullet.
Within the singleton clean sector the collision is impossible; proving
that global invariant is a separate obligation, not silently built
into the ghost.  No ghost bit is added to Agent.
-/

/-- The private all-zero candidate record. -/
def zeroCandidate : CPriv :=
  { C := false, alpha := false, m := false }

/-- Exactly the native and candidate fields owned by the two rows. -/
structure NativeCand where
  native : CertNative
  candidate : CPriv
  deriving DecidableEq, Repr

def NativeCand.ofAgent {c : Compiled} (a : Agent c) : NativeCand :=
  { native := a.certNative
    candidate := { C := a.C, alpha := a.alpha, m := a.m } }

/-- Base.cSelect with only its actually read fields exposed. -/
def nativeCandSelect (old : NativeCand)
    (postE : CertNative) (enter : Bool) : CSel :=
  let k2 :=
    old.candidate.C && old.candidate.alpha &&
      postE.b.val == 0 && postE.sg
  let safe := !postE.l && postE.b.val == 0
  if old.candidate.C && postE.l then CSel.SAN
  else if k2 then CSel.K2
  else if old.candidate.C && old.candidate.m && safe then CSel.PROM
  else if old.candidate.C && enter && !postE.sg &&
      old.candidate.alpha then CSel.DP2
  else if old.candidate.C && enter && !postE.sg &&
      !old.candidate.alpha then CSel.DP1
  else if old.candidate.C then CSel.KEEP
  else CSel.EMPTY

/-- Base.cPrivate with only the old candidate record exposed. -/
def nativeCandPrivate (old : NativeCand) : CSel → CPriv
  | .SAN => zeroCandidate
  | .K2 => zeroCandidate
  | .PROM => zeroCandidate
  | .DP2 => { C := true, alpha := true, m := true }
  | .DP1 => { C := true, alpha := true, m := old.candidate.m }
  | .KEEP => old.candidate
  | .EMPTY => zeroCandidate

def nativeCandNext (old : NativeCand)
    (postE : CertNative) (enter : Bool) : CPriv :=
  nativeCandPrivate old (nativeCandSelect old postE enter)

theorem nativeCandSelect_ofAgent {c : Compiled}
    (a : Agent c) (postE : CertNative) (enter : Bool) :
    nativeCandSelect (NativeCand.ofAgent a) postE enter =
      cSelect a postE enter := rfl

theorem nativeCandPrivate_ofAgent {c : Compiled}
    (a : Agent c) (sel : CSel) :
    nativeCandPrivate (NativeCand.ofAgent a) sel =
      cPrivate a sel := by
  cases sel <;> rfl

theorem nativeCandNext_ofAgent {c : Compiled}
    (a : Agent c) (postE : CertNative) (enter : Bool) :
    nativeCandNext (NativeCand.ofAgent a) postE enter =
      cPrivate a (cSelect a postE enter) := by
  rw [nativeCandNext, nativeCandSelect_ofAgent,
      nativeCandPrivate_ofAgent]

/-- The owner on two OLD native/candidate pairs.  ENTER is false for
the initiator and is computed from OLD fields for the responder. -/
def birthFreeCandidatePair (x y : NativeCand) :
    NativeCand × NativeCand :=
  let es := certLiteralEPair x.native y.native
  let enterY := !y.native.l && decide (outBullet x.native > 0)
  ({ native := es.1
     candidate := nativeCandNext x es.1 false },
   { native := es.2
     candidate := nativeCandNext y es.2 enterY })

/-- The selected-edge map.  Source priority agrees with nativeE and
PopulationProtocol.step, even for the degenerate one-site ring. -/
def birthFreeCandidateStep {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e : Fin n) :
    Fin n → NativeCand :=
  let j := ring.rightNeighbor e
  let pair := birthFreeCandidatePair (S e) (S j)
  fun i => if i = e then pair.1
           else if i = j then pair.2 else S i

def candidateNative {n : Nat}
    (S : Fin n → NativeCand) : Fin n → CertNative :=
  fun i => (S i).native

private theorem neighbor_ne_self {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem birthFreeCandidateStep_native {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e : Fin n) :
    candidateNative (birthFreeCandidateStep ring S e) =
      nativeE ring (candidateNative S) e := by
  funext i
  let j := ring.rightNeighbor e
  have hne : j ≠ e := neighbor_ne_self hn ring e
  by_cases he : i = e
  · subst i
    simp [candidateNative, birthFreeCandidateStep,
      birthFreeCandidatePair, nativeE, j]
  · by_cases hj : i = j
    · subst i
      simp [candidateNative, birthFreeCandidateStep,
        birthFreeCandidatePair, nativeE, he, hne, j]
    · simp [candidateNative, birthFreeCandidateStep,
        birthFreeCandidatePair, nativeE, he, hj, j]

/-! The real transition commutation. -/

/-- The exact OLD FIRE selection used inside Base.baseStep. -/
def oldFire {c : Compiled} (x y : Agent c) : Option FireSel :=
  let es := certLiteralEPair x.certNative y.certNative
  fireSelect x y es.1 es.2

private theorem projectAssemble {c : Compiled}
    (b cert hk : Agent c) :
    NativeCand.ofAgent (assemble b cert hk) =
      NativeCand.ofAgent b := rfl

private theorem discardPromGate {c : Compiled}
    (a : Agent c) (s : CSel) :
    (if s == CSel.PROM then zeroCandidate else cPrivate a s) =
      cPrivate a s := by
  cases s <;> rfl

/-- Field-level proof support: no native or candidate field is written
by PACK, BANK/SMALL, DCC, token movement or certificate assembly. -/
private theorem nativeCand_ext (a b : NativeCand)
    (hn : a.native = b.native)
    (hc : a.candidate = b.candidate) : a = b := by
  cases a with
  | mk na ca =>
    cases b with
    | mk nb cb =>
      cases hn
      cases hc
      rfl

private theorem agent_l_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).l =
      if p then a.l else b.l := by
  split <;> rfl

private theorem agent_b_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).b =
      if p then a.b else b.b := by
  split <;> rfl

private theorem agent_sh_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sh =
      if p then a.sh else b.sh := by
  split <;> rfl

private theorem agent_sg_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sg =
      if p then a.sg else b.sg := by
  split <;> rfl

private theorem agent_C_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).C =
      if p then a.C else b.C := by
  split <;> rfl

private theorem agent_alpha_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).alpha =
      if p then a.alpha else b.alpha := by
  split <;> rfl

private theorem agent_m_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).m =
      if p then a.m else b.m := by
  split <;> rfl

private theorem base_fst_l_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.l = (certLiteralEPair x.certNative y.certNative).1.l := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_l_ite]

private theorem base_fst_b_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.b = (certLiteralEPair x.certNative y.certNative).1.b := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_b_ite]

private theorem base_fst_sh_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.sh = (certLiteralEPair x.certNative y.certNative).1.sh := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_sh_ite]

private theorem base_fst_sg_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.sg = (certLiteralEPair x.certNative y.certNative).1.sg := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_sg_ite]

private theorem base_fst_C_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.C = (cPrivate x (cSelect x
        (certLiteralEPair x.certNative y.certNative).1 false)).C := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect x
      (certLiteralEPair x.certNative y.certNative).1 false <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_C_ite, cPrivate]

private theorem base_fst_alpha_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.alpha = (cPrivate x (cSelect x
        (certLiteralEPair x.certNative y.certNative).1 false)).alpha := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect x
      (certLiteralEPair x.certNative y.certNative).1 false <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_alpha_ite, cPrivate]

private theorem base_fst_m_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.m = (cPrivate x (cSelect x
        (certLiteralEPair x.certNative y.certNative).1 false)).m := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteX = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect x
      (certLiteralEPair x.certNative y.certNative).1 false <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_m_ite, cPrivate]

private theorem base_fst_native_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).1.certNative =
      (certLiteralEPair x.certNative y.certNative).1 := by
  change CertNative.mk
      (baseStep c ev x y).1.l
      (baseStep c ev x y).1.b
      (baseStep c ev x y).1.sh
      (baseStep c ev x y).1.sg = _
  rw [base_fst_l_noFire c ev x y hf,
      base_fst_b_noFire c ev x y hf,
      base_fst_sh_noFire c ev x y hf,
      base_fst_sg_noFire c ev x y hf]
  try rfl

private theorem base_fst_candidate_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (NativeCand.ofAgent (baseStep c ev x y).1).candidate =
      cPrivate x (cSelect x
        (certLiteralEPair x.certNative y.certNative).1 false) := by
  change CPriv.mk
      (baseStep c ev x y).1.C
      (baseStep c ev x y).1.alpha
      (baseStep c ev x y).1.m = _
  rw [base_fst_C_noFire c ev x y hf,
      base_fst_alpha_noFire c ev x y hf,
      base_fst_m_noFire c ev x y hf]
  try rfl

private theorem base_snd_l_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.l = (certLiteralEPair x.certNative y.certNative).2.l := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_l_ite]

private theorem base_snd_b_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.b = (certLiteralEPair x.certNative y.certNative).2.b := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_b_ite]

private theorem base_snd_sh_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.sh = (certLiteralEPair x.certNative y.certNative).2.sh := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_sh_ite]

private theorem base_snd_sg_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.sg = (certLiteralEPair x.certNative y.certNative).2.sg := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_sg_ite]

private theorem base_snd_C_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.C = (cPrivate y (cSelect y
        (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)))).C := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect y
      (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)) <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_C_ite, cPrivate]

private theorem base_snd_alpha_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.alpha = (cPrivate y (cSelect y
        (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)))).alpha := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect y
      (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)) <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_alpha_ite, cPrivate]

private theorem base_snd_m_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.m = (cPrivate y (cSelect y
        (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)))).m := by
  have hfire : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
    simpa [oldFire] using hf
  have hzero : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
      FireSite.siteY = false := by
    simp [hfire, fireAtSite]
  unfold baseStep
  cases hsel : cSelect y
      (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0)) <;>
  cases hs : c.useSmall <;>
    simp [hs, hfire, hzero, hsel, fireAtSite, Agent.setNative,
      Agent.setCPriv, agent_m_ite, cPrivate]

private theorem base_snd_native_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (baseStep c ev x y).2.certNative =
      (certLiteralEPair x.certNative y.certNative).2 := by
  change CertNative.mk
      (baseStep c ev x y).2.l
      (baseStep c ev x y).2.b
      (baseStep c ev x y).2.sh
      (baseStep c ev x y).2.sg = _
  rw [base_snd_l_noFire c ev x y hf,
      base_snd_b_noFire c ev x y hf,
      base_snd_sh_noFire c ev x y hf,
      base_snd_sg_noFire c ev x y hf]
  try rfl

private theorem base_snd_candidate_noFire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : oldFire x y = none) :
    (NativeCand.ofAgent (baseStep c ev x y).2).candidate =
      cPrivate y (cSelect y
        (certLiteralEPair x.certNative y.certNative).2 (!y.l && decide (outBullet x.certNative > 0))) := by
  change CPriv.mk
      (baseStep c ev x y).2.C
      (baseStep c ev x y).2.alpha
      (baseStep c ev x y).2.m = _
  rw [base_snd_C_noFire c ev x y hf,
      base_snd_alpha_noFire c ev x y hf,
      base_snd_m_noFire c ev x y hf]
  try rfl

/-- The exact native/candidate projection when FIRE is absent.
The DCC event may still be arbitrary, as in the full composed step. -/
theorem baseCandidate_noFire (c : Compiled) (ev : CertEvent)
    (x y : Agent c) (hf : oldFire x y = none) :
    (NativeCand.ofAgent (baseStep c ev x y).1,
     NativeCand.ofAgent (baseStep c ev x y).2) =
      birthFreeCandidatePair
        (NativeCand.ofAgent x) (NativeCand.ofAgent y) := by
  apply Prod.ext
  · apply nativeCand_ext
    · simpa [NativeCand.ofAgent, birthFreeCandidatePair]
        using base_fst_native_noFire c ev x y hf
    · have h := base_fst_candidate_noFire c ev x y hf
      rw [← nativeCandNext_ofAgent] at h
      simpa [NativeCand.ofAgent, birthFreeCandidatePair] using h
  · apply nativeCand_ext
    · simpa [NativeCand.ofAgent, birthFreeCandidatePair]
        using base_snd_native_noFire c ev x y hf
    · have h := base_snd_candidate_noFire c ev x y hf
      rw [← nativeCandNext_ofAgent] at h
      have hl : y.certNative.l = y.l := rfl
      simpa [NativeCand.ofAgent, birthFreeCandidatePair, hl] using h

/-- The certificate and H/K owners cannot overwrite native/candidate
fields: projection of the actual assembled transition. -/
theorem transitionCandidate_noFire (c : Compiled)
    (x y : Agent c) (hf : oldFire x y = none) :
    (NativeCand.ofAgent (transition c x y).1,
     NativeCand.ofAgent (transition c x y).2) =
      birthFreeCandidatePair
        (NativeCand.ofAgent x) (NativeCand.ofAgent y) := by
  calc
    _ =
      (NativeCand.ofAgent
          (baseStep c (certificateStep c x y).2.2 x y).1,
       NativeCand.ofAgent
          (baseStep c (certificateStep c x y).2.2 x y).2) := by
        cases hc : certificateStep c x y with
        | mk cx rest =>
          cases rest with
          | mk cy ev =>
            cases hh : hKStep c x y with
            | mk hx hy =>
              simp [transition, hc, hh, projectAssemble]
    _ = _ := baseCandidate_noFire c _ x y hf

/-! A first-credit ghost is an immutable OLD-edge snapshot. -/

/-- A witness records precisely which incoming edge was served,
the actual old native source/destination, and the emitted bullet
kind.  Its genuineness as a successful entry additionally requires
an empty old destination (rather than merely an ENTER attempt). -/
structure CandidateFirstEntry (n : Nat) where
  source : Fin n
  oldSource : CertNative
  oldDestination : CertNative
  bullet : Fin 3
  deriving DecidableEq, Repr

def CandidateFirstEntry.genuine {n : Nat}
    (w : CandidateFirstEntry n) : Prop :=
  w.oldDestination.l = false ∧
  w.oldDestination.b = (0 : Fin 3) ∧
  0 < outBullet w.oldSource ∧
  w.bullet.val = outBullet w.oldSource

/-- Ghost for a single candidate.  Erasure deletes the witness;
DP1 attaches this edge's actual snapshot; retention and DP2 keep
the earlier first-credit witness.  Source DP1 cannot occur because
ENTER_X is always false. -/
def nextCandidateGhost {n : Nat} (new : CPriv)
    (selection : CSel) (old : Option (CandidateFirstEntry n))
    (incoming : Option (CandidateFirstEntry n)) :
    Option (CandidateFirstEntry n) :=
  if new.C then
    if selection == CSel.DP1 then incoming else old
  else none

def candidateGhostStep {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand)
    (G : Fin n → Option (CandidateFirstEntry n))
    (e : Fin n) : Fin n → Option (CandidateFirstEntry n) :=
  let j := ring.rightNeighbor e
  let x := S e
  let y := S j
  let es := certLiteralEPair x.native y.native
  let enterY := !y.native.l && decide (outBullet x.native > 0)
  let sX := nativeCandSelect x es.1 false
  let sY := nativeCandSelect y es.2 enterY
  let next := birthFreeCandidatePair x y
  let actualSnapshot : CandidateFirstEntry n :=
    { source := e
      oldSource := x.native
      oldDestination := y.native
      bullet := certFinThree (outBullet x.native) }
  fun i =>
    if i = e then
      nextCandidateGhost next.1.candidate sX (G e) none
    else if i = j then
      nextCandidateGhost next.2.candidate sY (G j)
        (some actualSnapshot)
    else G i

/-! Genuine-history hull.  The origin hypotheses cannot be skipped. -/

def OneNativeLeader {n : Nat}
    (N : Fin n → CertNative) : Prop :=
  ∃ p : Fin n, (N p).l = true ∧
    ∀ i : Fin n, (N i).l = true → i = p

/-- Paper credit-clean origin: singleton C_native, leader's
candidate record zero, and every follower alpha=m=0. -/
def CandidateCreditClean {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand) : Prop :=
  OneNativeLeader (candidateNative S) ∧
  C_native ring (candidateNative S) ∧
  (∀ i : Fin n,
    (S i).candidate.alpha = false ∧
    (S i).candidate.m = false ∧
    ((S i).native.l = true → (S i).candidate.C = false))

/-- The only base constructor is an actual credit-clean origin with
empty ghosts.  Every later constructor is an actual birth-free edge.
There is NO arbitrary-state injection or unconstrained history oracle. -/
inductive CandidateHistory {n : Nat} (ring : DirectedRing n) :
    (Fin n → NativeCand) →
    (Fin n → Option (CandidateFirstEntry n)) → Prop where
  | origin (S : Fin n → NativeCand)
      (h : CandidateCreditClean ring S) :
      CandidateHistory ring S (fun _ => none)
  | next {S : Fin n → NativeCand}
      {G : Fin n → Option (CandidateFirstEntry n)}
      (h : CandidateHistory ring S G) (e : Fin n) :
      CandidateHistory ring
        (birthFreeCandidateStep ring S e)
        (candidateGhostStep ring S G e)

/-- The paper's physical generated class is the existential
projection of genuine ghost-annotated histories. -/
def H_cand {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand) : Prop :=
  ∃ G : Fin n → Option (CandidateFirstEntry n),
    CandidateHistory ring S G

theorem H_cand_origin {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand)
    (h : CandidateCreditClean ring S) :
    H_cand ring S :=
  ⟨fun _ => none, CandidateHistory.origin S h⟩

/-- Exact one-edge closure of the generated history hull.
The same witness is extended; a new origin is NOT assumed. -/
theorem H_cand_birthFree_step {n : Nat} (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e : Fin n)
    (h : H_cand ring S) :
    H_cand ring (birthFreeCandidateStep ring S e) := by
  obtain ⟨G, hG⟩ := h
  exact ⟨candidateGhostStep ring S G e, CandidateHistory.next hG e⟩

/-! Candidate emptiness and the precise DP2 obstruction. -/

def EmptyCandidates {n : Nat} (S : Fin n → NativeCand) : Prop :=
  ∀ i : Fin n, (S i).candidate = zeroCandidate

theorem nativeCandNext_empty (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (h : old.candidate = zeroCandidate) :
    nativeCandNext old postE enter = zeroCandidate := by
  simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
    h, zeroCandidate]

private theorem birthFreePair_empty (x y : NativeCand)
    (hx : x.candidate = zeroCandidate)
    (hy : y.candidate = zeroCandidate) :
    (birthFreeCandidatePair x y).1.candidate = zeroCandidate ∧
    (birthFreeCandidatePair x y).2.candidate = zeroCandidate := by
  constructor
  · exact nativeCandNext_empty x
      (certLiteralEPair x.native y.native).1 false hx
  · exact nativeCandNext_empty y
      (certLiteralEPair x.native y.native).2
      (!y.native.l && decide (outBullet x.native > 0)) hy

theorem EmptyCandidates_step {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (S : Fin n → NativeCand) (e : Fin n)
    (h : EmptyCandidates S) :
    EmptyCandidates (birthFreeCandidateStep ring S e) := by
  intro i
  let j := ring.rightNeighbor e
  have hne : j ≠ e := neighbor_ne_self hn ring e
  have hp := birthFreePair_empty (S e) (S j) (h e) (h j)
  by_cases he : i = e
  · subst i
    simpa [birthFreeCandidateStep, j] using hp.1
  · by_cases hj : i = j
    · subst i
      simpa [birthFreeCandidateStep, j, he, hne] using hp.2
    · simpa [birthFreeCandidateStep, j, he, hj] using h i

/-- The empty candidate projection is preserved. The native geometry
is a separate obligation, not a hidden premise of this theorem. -/
theorem H_cand_empty_step {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (S : Fin n → NativeCand) (e : Fin n)
    (h : H_cand ring S ∧ EmptyCandidates S) :
    H_cand ring (birthFreeCandidateStep ring S e) ∧
      EmptyCandidates (birthFreeCandidateStep ring S e) :=
  ⟨H_cand_birthFree_step ring S e h.1,
    EmptyCandidates_step ring hn S e h.2⟩

/-- This isolates the only direct creator of a mature bit: DP2.
To rule DP2 out in H_cand needs the global signal-return argument. -/
theorem nativeCandNext_m_false_of_noSecondDP
    (old : NativeCand) (postE : CertNative) (enter : Bool)
    (hm : old.candidate.m = false)
    (hd : nativeCandSelect old postE enter ≠ CSel.DP2) :
    (nativeCandNext old postE enter).m = false := by
  cases hs : nativeCandSelect old postE enter with
  | SAN => simp [nativeCandNext, nativeCandPrivate, hs, zeroCandidate]
  | K2 => simp [nativeCandNext, nativeCandPrivate, hs, zeroCandidate]
  | PROM => simp [nativeCandNext, nativeCandPrivate, hs, zeroCandidate]
  | DP2 => exact False.elim (hd hs)
  | DP1 => simpa [nativeCandNext, nativeCandPrivate, hs] using hm
  | KEEP => simpa [nativeCandNext, nativeCandPrivate, hs] using hm
  | EMPTY => simp [nativeCandNext, nativeCandPrivate, hs, zeroCandidate]

/-! Real full-protocol step, guarded by its actual OLD FIRE test. -/

/-- Unlike a fabricated arbitrary projection step, this is the
PopulationProtocol.step applied to protocol q. -/
theorem H_cand_real_noFire {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : H_cand ring (fun i => NativeCand.ofAgent (C i))) :
    H_cand ring
      (fun i => NativeCand.ofAgent
        (PopulationProtocol.step (protocol q) ring C e i)) := by
  have hp :=
    transitionCandidate_noFire (compileAdvice q)
      (C e) (C (ring.rightNeighbor e)) hfire
  have hne : ring.rightNeighbor e ≠ e :=
    neighbor_ne_self hn ring e
  have hproj :
      (fun i => NativeCand.ofAgent
        (PopulationProtocol.step (protocol q) ring C e i)) =
      birthFreeCandidateStep ring
        (fun i => NativeCand.ofAgent (C i)) e := by
    funext i
    by_cases he : i = e
    · subst i
      simpa [PopulationProtocol.step, protocol,
        birthFreeCandidateStep]
        using congrArg Prod.fst hp
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa [PopulationProtocol.step, protocol,
          birthFreeCandidateStep, he, hne]
          using congrArg Prod.snd hp
      · simp [PopulationProtocol.step, protocol,
          birthFreeCandidateStep, he, hj]
  rw [hproj]
  exact H_cand_birthFree_step ring _ e h

/-! A concrete n=5 credit-clean singleton with no candidate. -/

private theorem candidateFiveRing : DirectedRing 5 := ⟨by decide⟩

private def candidateFiveFollower : CertNative :=
  { l := false, b := 0, sh := false, sg := false }

def fiveCandidateOrigin : Fin 5 → NativeCand :=
  fun i =>
    { native :=
        if i.val == 0 then
          { l := true, b := 0, sh := true, sg := false }
        else candidateFiveFollower
      candidate := zeroCandidate }

theorem fiveCandidateOrigin_creditClean :
    CandidateCreditClean candidateFiveRing fiveCandidateOrigin := by
  unfold CandidateCreditClean
  constructor
  · refine ⟨(0 : Fin 5), ?_, ?_⟩
    · decide
    · intro i hi
      have hz : i.val = 0 := by
        by_cases hzero : i.val = 0
        · exact hzero
        · simp [candidateNative, fiveCandidateOrigin,
            candidateFiveFollower, hzero] at hi
      exact Fin.ext hz
  constructor
  · decide +kernel
  · intro i
    exact ⟨rfl, rfl, fun _ => rfl⟩

theorem fiveCandidateOrigin_generated :
    H_cand candidateFiveRing fiveCandidateOrigin :=
  H_cand_origin candidateFiveRing fiveCandidateOrigin
    fiveCandidateOrigin_creditClean

theorem fiveCandidateOrigin_empty :
    EmptyCandidates fiveCandidateOrigin := by
  intro i
  rfl

theorem fiveCandidateOrigin_nonempty :
    OneNativeLeader (candidateNative fiveCandidateOrigin) ∧
    C_native candidateFiveRing (candidateNative fiveCandidateOrigin) ∧
    H_cand candidateFiveRing fiveCandidateOrigin ∧
    EmptyCandidates fiveCandidateOrigin :=
  ⟨fiveCandidateOrigin_creditClean.1,
   fiveCandidateOrigin_creditClean.2.1,
   fiveCandidateOrigin_generated, fiveCandidateOrigin_empty⟩

/-- Concrete native-sector control at n=5 for every edge of this
one specific clean origin; not a universal arbitrary-n closure theorem. -/
theorem fiveCandidateOrigin_native_step_clean (e : Fin 5) :
    C_native candidateFiveRing
      (nativeE candidateFiveRing (candidateNative fiveCandidateOrigin) e) := by
  have h : e = (0 : Fin 5) ∨ e = (1 : Fin 5) ∨
      e = (2 : Fin 5) ∨ e = (3 : Fin 5) ∨
      e = (4 : Fin 5) := by
    rcases e with ⟨v, hv⟩
    rcases v with _ | _ | _ | _ | _ | v
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · omega
  rcases h with h | h | h | h | h
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel

end L3
