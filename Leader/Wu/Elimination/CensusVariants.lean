import Leader.Wu.Birth.TransitShiftVariants

/-!
# Elimination-stage variants for the closure census (board G6.2, design input)

The census pipelines `PPLLBirthPatch.pipeline` (PPLLBirthPatch.lean:151) and
`PPLLBirthPatchM2.pipeline` (PPLLBirthPatchM2.lean:169) end with the research
repair `eliminateLeadersNoCollision` (Repairs.lean:289, ERRATA T7).  This module
restates both pipelines with the Algorithm-15 stage chosen by a switch, so the
census can compare the repair with the source transcription
`PPLL.eliminateLeaders` (Algorithm.lean:600; thesis Algorithm 15, p.32 /
PDF p.45).  With `Elim.noCollision` each pipeline here is stage-for-stage the
pipeline it restates; the census checks this empirically by reproducing the
original closures.  No proof content; no existing module is edited.
-/

set_option autoImplicit false

namespace PPLLElimVariants

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2

/-- Which Algorithm-15 stage ends the pipeline. -/
inductive Elim where
  | noCollision -- `eliminateLeadersNoCollision` (Repairs.lean:289), T7 repair
  | source      -- `eliminateLeaders` (Algorithm.lean:600), literal Algorithm 15
  | egressSink  -- `eliminateLeadersNoCollisionEgressSink` (MultiLeaderCleanup.lean:101)
  | k2          -- `LDSinkKernelC.sinkKernelC` (LDSinkKernelC.lean:34), ERRATA R160 kernel K2
  deriving DecidableEq

/-- Restatement of `eliminateLeadersNoCollisionEgressSink`
(MultiLeaderCleanup.lean:101-111): FIRE, zero-leader egress MOVE, leader-sink
SIGNAL (clamp kept), dummy sink.  Restated because that module's import
closure is far larger than the census build stages. -/
def egressSinkKernel {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nextLabel q1.1 q1.2
  dummyBulletSink q2

/-- Restatement of `LDSinkKernelC.absorbProtectedMove` (LDSinkKernelC.lean:24-30):
a live follower bullet arriving at a shielded leader is absorbed. -/
def absorbProtectedMove {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3) then
    (l, { r with bullet := (0 : Fin 3) })
  else
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r

/-- Restatement of `LDSinkKernelC.sinkKernelC` (LDSinkKernelC.lean:34-41), the
kernel K2 adopted in ERRATA R160. -/
def k2Kernel {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  dummyBulletSink q2

def elimStage {ψ : Nat} (hψ : ψ > 0) (e : Elim) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match e with
  | .noCollision => eliminateLeadersNoCollision hψ l r
  | .source => eliminateLeaders hψ l r
  | .egressSink => egressSinkKernel hψ l r
  | .k2 => k2Kernel hψ l r

/-- `PPLLBirthPatch.pipeline` with the elimination stage chosen. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (consume : Bool) (cmp : Cmp)
    (protect readyGuard : Bool) (e : Elim) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveWith hψ consume q.1 q.2
  let q := checkSigWith hψ readyGuard q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigWith hψ cmp protect q.1 q.2
  let q := suppressSig hψ q.1 q.2
  let q := elimStage hψ e q.1 q.2
  writeSeq hψ q.1 q.2

/-- `PPLLBirthPatchM2.pipeline` with the elimination stage chosen. -/
def pipelineM2 {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (cmp : Cmp) (m : M2) (e : Elim)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveM2 hψ m q.1 q.2
  let q := if m = .dropMisaligned then (dropStale q.1, dropStale q.2) else q
  let q := checkSigWith hψ true q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigM2 hψ cmp m q.1 q.2
  let q := suppressSig hψ q.1 q.2
  let q := elimStage hψ e q.1 q.2
  writeSeq hψ q.1 q.2

/-- Named variants.  `none` for the M2 slot selects the `PPLLBirthPatch`
pipeline with `(consume, cmp, protect, readyGuard)`; `some m` selects the M2
pipeline with `cmp` and `m` (the other switches are ignored). -/
def variants : List (String × Bool × Cmp × Bool × Bool × Option M2 × Elim) :=
  [ ("elimBoundedNoCol", false, .original, false, false, none, .noCollision)
  , ("elimBoundedSrc", false, .original, false, false, none, .source)
  , ("elimIntegratedNoCol", false, .noSourceRearm, false, false, none, .noCollision)
  , ("elimIntegratedSrc", false, .noSourceRearm, false, false, none, .source)
  , ("elimBoundedM1NoCol", false, .original, false, false, some .none, .noCollision)
  , ("elimBoundedM1Src", false, .original, false, false, some .none, .source)
  , ("elimIntegratedM1NoCol", false, .leaderlessRearm, false, false, some .none, .noCollision)
  , ("elimIntegratedM1Src", false, .leaderlessRearm, false, false, some .none, .source)
  , ("elimBoundedEgress", false, .original, false, false, none, .egressSink)
  , ("elimBoundedK2", false, .original, false, false, none, .k2)
  , ("elimIntegratedEgress", false, .noSourceRearm, false, false, none, .egressSink)
  , ("elimIntegratedK2", false, .noSourceRearm, false, false, none, .k2)
  , ("elimBoundedM1K2", false, .original, false, false, some .none, .k2)
  , ("elimIntegratedM1K2", false, .leaderlessRearm, false, false, some .none, .k2) ]

def run {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (t : Bool × Cmp × Bool × Bool × Option M2 × Elim) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (consume, cmp, protect, readyGuard, m2, e) := t
  match m2 with
  | none => pipeline hψ κ consume cmp protect readyGuard e l r
  | some m => pipelineM2 hψ κ cmp m e l r

end PPLLElimVariants
