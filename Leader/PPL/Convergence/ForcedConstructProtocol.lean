import Leader.PPL.SPLEntry.ForcingWord
import Leader.PPL.Convergence.ConstructCoupling

/-!
# One paper-canonical definition of P_PL'

The paper defines P_PL' by forcing the Construct branch only in mode-dependent
commands of Algorithms 2 and 3; DetermineMode and EliminateLeaders remain
literal (`sources/ppl-podc2023/paper.txt`, lines 1118–1129). This agrees with
R7's post-DetermineMode boundary and its warning that pre-state mode is not
enough (`design/PPL_ARCHITECTURE_BRIEF.md`, R7 item 7).
-/

namespace PPL.Convergence.PrimeUnify

set_option autoImplicit false
set_option Elab.async false

/-- The two local transition implementations of the paper's P_PL' coincide. -/
private def paperLine4Tmp {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) : Fin (2 * psi) :=
  let d := PPL.determineMode l r
  if d.2.leader = true then
    ⟨0, by omega⟩
  else
    ⟨(d.1.dist.val + 1) % (2 * psi), Nat.mod_lt _ (by omega)⟩

private theorem paperLine4Tmp_eq_throughLine6
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    paperLine4Tmp hpsi l r = (PPL.createLeaderThroughLine6 hpsi l r).tmp := by
  dsimp only [paperLine4Tmp, PPL.createLeaderThroughLine6]
  rfl

private theorem state_setMode_eq_of_eq
    {psi kappa : Nat} (s : PPL.State psi kappa) (m : Bool)
    (hm : s.mode = m) :
    {s with mode := m} = s := by
  cases s
  simp_all

private def paperConstructCreateLeader {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let d := PPL.determineMode l r
  let tmp := (PPL.createLeaderThroughLine6 hpsi l r).tmp
  let r0 : PPL.State psi kappa :=
    { d.2 with dist := tmp, mode := false }
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if r0.dist.val = 0 ∨ r0.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }
  let b := PPL.moveToken hpsi .black l0 r0
  let w := PPL.moveToken hpsi .white b.1 b.2
  (w.1, { w.2 with mode := d.2.mode })

private theorem two_pprimeMoveToken_eq_paperConstruct
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.Convergence.L18.pprimeMoveToken hpsi .white
        (PPL.Convergence.L18.pprimeMoveToken hpsi .black l r).1
        (PPL.Convergence.L18.pprimeMoveToken hpsi .black l r).2 =
      let r0 := { r with mode := false }
      let b := PPL.moveToken hpsi .black l r0
      let w := PPL.moveToken hpsi .white b.1 b.2
      (w.1, { w.2 with mode := r.mode }) := by
  let r0 : PPL.State psi kappa := { r with mode := false }
  let b := PPL.moveToken hpsi .black l r0
  let w := PPL.moveToken hpsi .white b.1 b.2
  have hbmode : b.2.mode = false := by
    exact (PPL.Convergence.ConstructCoupling.moveToken_modes
      hpsi .black l r0).2
  have hreset : ({b.2 with mode := false} : PPL.State psi kappa) = b.2 := by
    cases hb : b.2
    simp_all
  have hroundtrip :
      ({ {b.2 with mode := r.mode} with mode := false} : PPL.State psi kappa) = b.2 := by
    calc
      { {b.2 with mode := r.mode} with mode := false } =
          {b.2 with mode := false} := rfl
      _ = b.2 := hreset
  change
    (let q := PPL.moveToken hpsi .white b.1
        { {b.2 with mode := r.mode} with mode := false };
      (q.1, {q.2 with mode := r.mode})) =
      (w.1, {w.2 with mode := r.mode})
  rw [hroundtrip]

private theorem l18CreateLeader_eq_paperConstruct
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.Convergence.L18.pprimeCreateLeader hpsi l r =
      paperConstructCreateLeader hpsi l r := by
  let d := PPL.determineMode l r
  simp only [PPL.Convergence.L18.pprimeCreateLeader,
    paperConstructCreateLeader]
  change
    (let tmp := paperLine4Tmp hpsi l r
      let r' := {(PPL.determineMode l r).2 with dist := tmp}
      let l' :=
        if r'.leader = true then
          {(PPL.determineMode l r).1 with last := true}
        else if r'.dist.val = 0 ∨ r'.dist.val = psi then
          {(PPL.determineMode l r).1 with last := false}
        else
          {(PPL.determineMode l r).1 with last := r'.last}
      PPL.Convergence.L18.pprimeMoveToken hpsi .white
        (PPL.Convergence.L18.pprimeMoveToken hpsi .black l' r').1
        (PPL.Convergence.L18.pprimeMoveToken hpsi .black l' r').2) =
      paperConstructCreateLeader hpsi l r
  rw [two_pprimeMoveToken_eq_paperConstruct]
  rfl

private theorem createLeaderPrime_eq_paperConstruct
    {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.Convergence.ConstructCoupling.createLeaderPrime hpsi l r =
      paperConstructCreateLeader hpsi l r := by
  by_cases hmode : (PPL.determineMode l r).2.mode = false
  · rw [PPL.Convergence.ConstructCoupling.createLeaderPrime_eq_createLeader_of_postConstruct
      hpsi l r hmode]
    have hguard : PPL.createLeaderLine6Guard hpsi l r = False := by
      simp [PPL.createLeaderLine6Guard, hmode]
    let d := PPL.determineMode l r
    let tmp := (PPL.createLeaderThroughLine6 hpsi l r).tmp
    let r0 : PPL.State psi kappa := {d.2 with dist := tmp, mode := false}
    let l0 : PPL.State psi kappa :=
      if r0.leader = true then
        {d.1 with last := true}
      else if r0.dist.val = 0 ∨ r0.dist.val = psi then
        {d.1 with last := false}
      else
        {d.1 with last := r0.last}
    let b := PPL.moveToken hpsi .black l0 r0
    let w := PPL.moveToken hpsi .white b.1 b.2
    have hbmode : b.2.mode = false := by
      rw [(PPL.Convergence.ConstructCoupling.moveToken_modes
        hpsi .black l0 r0).2]
    have hwmode : w.2.mode = false := by
      rw [(PPL.Convergence.ConstructCoupling.moveToken_modes
        hpsi .white b.1 b.2).2, hbmode]
    have hrestore : {w.2 with mode := false} = w.2 :=
      state_setMode_eq_of_eq w.2 false hwmode
    unfold PPL.createLeader paperConstructCreateLeader
    simp only [PPL.createLeaderThroughLine6, hguard, if_false, if_true, hmode]
    apply Prod.ext
    · rfl
    · change w.2 = {w.2 with mode := false}
      exact hrestore.symm
  · simp only [PPL.Convergence.ConstructCoupling.createLeaderPrime,
      if_neg hmode]
    rfl

theorem pprimeTransition_eq_transitionPrime (psi kappa : Nat) :
    PPL.Convergence.L18.pprimeTransition psi kappa =
      PPL.Convergence.ConstructCoupling.transitionPrime psi kappa := by
  funext l r
  by_cases hpsi : 2 ≤ psi
  · simp [PPL.Convergence.L18.pprimeTransition,
      PPL.Convergence.ConstructCoupling.transitionPrime, hpsi,
      PPL.Convergence.L18.pprimePpl,
      PPL.Convergence.ConstructCoupling.pplPrime,
      l18CreateLeader_eq_paperConstruct,
      createLeaderPrime_eq_paperConstruct]
  · simp [PPL.Convergence.L18.pprimeTransition,
      PPL.Convergence.ConstructCoupling.transitionPrime, hpsi]

/-- The per-edge executable steps inherit equality from the shared transition. -/
theorem pprimeStep_eq_primeStep
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : PPL.Config n psi kappa) (e : Fin n) :
    PPL.Convergence.L18.pprimeStep ring C e =
      PPL.Convergence.ConstructCoupling.primeStep ring C e := by
  simp [PPL.Convergence.L18.pprimeStep,
    PPL.Convergence.ConstructCoupling.primeStep,
    PopulationProtocol.step,
    PPL.Convergence.L18.pprimeProtocol,
    PPL.Convergence.ConstructCoupling.protocolPrime,
    pprimeTransition_eq_transitionPrime]
  funext k
  rfl

/-- The recursive L18 runner and the ConstructCoupling population runner are
extensionally the same on every schedule and starting configuration. -/
theorem runPPrime_eq_runPrime
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : PPL.Config n psi kappa) (word : DetSchedule n) :
    PPL.Convergence.L18.runPPrime ring C word =
      PPL.Convergence.ConstructCoupling.runPrime ring C word := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [PPL.Convergence.L18.runPPrime,
        PPL.Convergence.ConstructCoupling.runPrime,
        PPL.Probability.runPopulationSchedule]
      rw [pprimeStep_eq_primeStep]
      exact ih (PPL.Convergence.ConstructCoupling.primeStep ring C e)

#print axioms PPL.Convergence.PrimeUnify.pprimeTransition_eq_transitionPrime
#print axioms PPL.Convergence.PrimeUnify.pprimeStep_eq_primeStep
#print axioms PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime

end PPL.Convergence.PrimeUnify
