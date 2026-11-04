import Leader.PPL.Safety.PeacefulKeep
import Leader.PPL.Elim.RowE
import Leader.PPL.TransitionFacts

namespace PPL.Safety.PeacefulProps

set_option autoImplicit false

abbrev Cell4 := PPL.Elim.Cell4

def born4 : Cell4 :=
  {
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false
  }

def project4
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    Fin n → Cell4 :=
  PPL.Elim.viewConfig C

def Peaceful4
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n → Cell4)
    (i : Fin n) : Prop :=
  PPL.PeacefulCore ring
    (fun j => (D j).leader)
    (fun j => (D j).shield)
    (fun j => (D j).signalB)
    i

def PB4
    {n : Nat}
    (ring : DirectedRing n)
    (D : Fin n → Cell4) : Prop :=
  PPL.CPBCore ring
    (fun i => (D i).leader)
    (fun i => (D i).bullet)
    (fun i => (D i).shield)
    (fun i => (D i).signalB)

/--
Exact first part of CreateLeader, through Algorithm-2 line 9 and before the
two MoveToken calls.  It is definitionally the prefix of PPL.createLeader.
-/
def preTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l := s.left
  let r := s.right
  let tmp := s.tmp
  let r :=
    if r.mode = false then
      { r with dist := tmp }
    else
      r
  let l :=
    if r.leader = true then
      { l with last := true }
    else if Or (r.dist.val = 0) (r.dist.val = psi) then
      { l with last := false }
    else
      { l with last := r.last }
  (l, r)

/--
A full four-field step changes only the scheduled endpoints and, at those
endpoints, has exactly one of two causal shapes:

* no CreateLeader birth: rowE(pre-left, pre-right);
* a CreateLeader birth on the responder: rowE(pre-left, born4).

The second branch covers both Algorithm-2 line 6 and Algorithm-3 line 20,
which write the same leaderBirth four-field value.
-/
def FourFieldStepCase
    {n : Nat}
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n) : Prop :=
  let j := ring.rightNeighbor e
  And
    (∀ k : Fin n,
      k ≠ e →
      k ≠ j →
      D' k = D k)
    (Or
      (And
        (D' e =
          (PPL.Elim.rowE (D e) (D j)).1)
        (D' j =
          (PPL.Elim.rowE (D e) (D j)).2))
      (And
        (D' e =
          (PPL.Elim.rowE (D e) born4).1)
        (D' j =
          (PPL.Elim.rowE (D e) born4).2)))

/--
The single remaining scan-locality leaf.

This statement is entirely on the exact four-field quotient.  It is exactly
what scripts/ppl_peaceful_props_check.py exhaustively checked for n=3,4:
leader survival from PB4, genuine-new-live peacefulness, and preservation of
an old peaceful live bullet at its same/moved survival locations.

No 13-field transition fact is hidden here; FourFieldStepCase is supplied by
step_fourField_cases below.
-/
def PeacefulScanLocalityProp : Prop :=
  ∀ {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (D D' : Fin n → Cell4)
    (e : Fin n),
    FourFieldStepCase ring D D' e →
    And
      (PB4 ring D →
        ∃ i : Fin n,
          (D' i).leader = true)
      (And
        (∀ i : Fin n,
          (D' i).bullet = (2 : Fin 3) →
          (D i).bullet ≠ (2 : Fin 3) →
          Or
            (i ≠ ring.rightNeighbor e)
            ((D e).bullet ≠ (2 : Fin 3)) →
          Peaceful4 ring D' i)
        (∀ i : Fin n,
          (D i).bullet = (2 : Fin 3) →
          Peaceful4 ring D i →
          And
            ((D' i).bullet = (2 : Fin 3) →
              Peaceful4 ring D' i)
            (i = e →
              (D' (ring.rightNeighbor e)).bullet = (2 : Fin 3) →
              (D (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) →
              Peaceful4 ring D' (ring.rightNeighbor e))))

theorem step_fourField_cases
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    let C' :=
      PopulationProtocol.step (PPL.protocol psi kappa) ring C e
    FourFieldStepCase ring (project4 C) (project4 C') e := by
  dsimp only
  let j := ring.rightNeighbor e
  let l := C e
  let r := C j
  have hne : j ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    change (e.val + 1) % n = e.val at hv
    by_cases hs : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt hs] at hv
      omega
    · have heq : e.val + 1 = n := by
        omega
      rw [heq, Nat.mod_self] at hv
      omega
  have hpre :
      ∀ a b : State psi kappa,
        let p := preTokenPair hpsi a b
        And
          (PPL.Elim.view4 p.1 = PPL.Elim.view4 a)
          (Or
            (PPL.Elim.view4 p.2 = PPL.Elim.view4 b)
            (PPL.Elim.view4 p.2 = born4)) := by
    intro a b
    have hdet :
        let q := PPL.determineMode a b
        PPL.Elim.view4 q.1 = PPL.Elim.view4 a ∧
        PPL.Elim.view4 q.2 = PPL.Elim.view4 b := by
      simp only [PPL.determineMode]
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals exact ⟨rfl, rfl⟩
    dsimp only at hdet
    let s := PPL.createLeaderThroughLine6 hpsi a b
    have hline6 :
        PPL.Elim.view4 s.left = PPL.Elim.view4 a ∧
        (PPL.Elim.view4 s.right = PPL.Elim.view4 b ∨
          PPL.Elim.view4 s.right = born4) := by
      dsimp only [s, PPL.createLeaderThroughLine6]
      split
      · exact ⟨hdet.1, Or.inr rfl⟩
      · exact ⟨hdet.1, Or.inl hdet.2⟩
    have hline89 :
        let p := preTokenPair hpsi a b
        PPL.Elim.view4 p.1 = PPL.Elim.view4 s.left ∧
        PPL.Elim.view4 p.2 = PPL.Elim.view4 s.right := by
      dsimp only [preTokenPair]
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals try (split <;> try dsimp only)
      all_goals exact ⟨rfl, rfl⟩
    dsimp only at hline89 ⊢
    constructor
    · exact hline89.1.trans hline6.1
    · rcases hline6.2 with hb | hb
      · exact Or.inl (hline89.2.trans hb)
      · exact Or.inr (hline89.2.trans hb)
  have hmove :
      ∀ (kind : PPL.TokenKind) (a b : State psi kappa),
        let q := PPL.moveToken hpsi kind a b
        And
          (PPL.Elim.view4 q.1 = PPL.Elim.view4 a)
          (Or
            (PPL.Elim.view4 q.2 = PPL.Elim.view4 b)
            (PPL.Elim.view4 q.2 = born4)) := by
    intro kind a b
    dsimp only
    simpa [born4] using PPL.moveToken_view4_cases hpsi kind a b
  have hcreate :
      let q := PPL.createLeader hpsi l r
      And
        (PPL.Elim.view4 q.1 = PPL.Elim.view4 l)
        (Or
          (PPL.Elim.view4 q.2 = PPL.Elim.view4 r)
          (PPL.Elim.view4 q.2 = born4)) := by
    let p := preTokenPair hpsi l r
    let b := PPL.moveToken hpsi .black p.1 p.2
    let w := PPL.moveToken hpsi .white b.1 b.2
    have hdef :
        PPL.createLeader hpsi l r = w := by
      rfl
    have hp := hpre l r
    have hb := hmove PPL.TokenKind.black p.1 p.2
    have hw := hmove PPL.TokenKind.white b.1 b.2
    dsimp only at hp hb hw
    rw [hdef]
    constructor
    · exact hw.1.trans (hb.1.trans hp.1)
    · rcases hp.2 with hpR | hpR
      · rcases hb.2 with hbR | hbR
        · rcases hw.2 with hwR | hwR
          · exact Or.inl (hwR.trans (hbR.trans hpR))
          · exact Or.inr hwR
        · rcases hw.2 with hwR | hwR
          · exact Or.inr (hwR.trans hbR)
          · exact Or.inr hwR
      · rcases hb.2 with hbR | hbR
        · rcases hw.2 with hwR | hwR
          · exact Or.inr (hwR.trans (hbR.trans hpR))
          · exact Or.inr hwR
        · rcases hw.2 with hwR | hwR
          · exact Or.inr (hwR.trans hbR)
          · exact Or.inr hwR
  let q := PPL.createLeader hpsi l r
  have htrans :
      PPL.transition psi kappa l r =
        PPL.eliminateLeaders q.1 q.2 := by
    simpa only [PPL.ppl, q] using
      (PPL.transition_eq_ppl hpsi l r)
  have hpair :
      Or
        ((PPL.Elim.view4
              (PPL.transition psi kappa l r).1,
            PPL.Elim.view4
              (PPL.transition psi kappa l r).2) =
          PPL.Elim.rowE
            (PPL.Elim.view4 l)
            (PPL.Elim.view4 r))
        ((PPL.Elim.view4
              (PPL.transition psi kappa l r).1,
            PPL.Elim.view4
              (PPL.transition psi kappa l r).2) =
          PPL.Elim.rowE
            (PPL.Elim.view4 l)
            born4) := by
    dsimp only at hcreate
    rcases hcreate.2 with hr | hr
    · left
      have hrow :=
        PPL.Elim.view4_eliminateLeaders_pair q.1 q.2
      rw [hcreate.1, hr] at hrow
      simpa [htrans] using hrow
    · right
      have hrow :=
        PPL.Elim.view4_eliminateLeaders_pair q.1 q.2
      rw [hcreate.1, hr] at hrow
      simpa [htrans] using hrow
  change
    FourFieldStepCase ring
      (project4 C)
      (project4
        (PopulationProtocol.step
          (PPL.protocol psi kappa) ring C e))
      e
  dsimp [FourFieldStepCase]
  refine And.intro ?_ ?_
  · intro k hke hkj
    simp [project4, PPL.Elim.viewConfig,
      PopulationProtocol.step, PPL.protocol, hke, hkj, j]
  · rcases hpair with hpair | hpair
    · left
      constructor
      · have hf := congrArg Prod.fst hpair
        simpa [project4, PPL.Elim.viewConfig,
          PopulationProtocol.step, PPL.protocol, l, r, j]
          using hf
      · have hs := congrArg Prod.snd hpair
        simpa [project4, PPL.Elim.viewConfig,
          PopulationProtocol.step, PPL.protocol, l, r, j, hne]
          using hs
    · right
      constructor
      · have hf := congrArg Prod.fst hpair
        simpa [project4, PPL.Elim.viewConfig,
          PopulationProtocol.step, PPL.protocol, l, r, j]
          using hf
      · have hs := congrArg Prod.snd hpair
        simpa [project4, PPL.Elim.viewConfig,
          PopulationProtocol.step, PPL.protocol, l, r, j, hne]
          using hs

theorem cpbLeaderSurvival
    (hscan : PeacefulScanLocalityProp) :
    PPL.CPBLeaderSurvivalProp := by
  intro n psi kappa hn3 hpsi ring C e hC
  let C' : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring C e
  have hshape :
      FourFieldStepCase ring
        (project4 C)
        (project4 C')
        e := by
    simpa [C'] using
      step_fourField_cases hn3 hpsi ring C e
  have hq :=
    hscan hn3 ring
      (project4 C)
      (project4 C')
      e
      hshape
  have hPB : PB4 ring (project4 C) := by
    change PPL.CPBCore ring
      (fun i => (C i).leader)
      (fun i => (C i).bullet)
      (fun i => (C i).shield)
      (fun i => (C i).signalB)
    exact hC
  obtain ⟨i, hi⟩ := hq.1 hPB
  refine ⟨i, ?_⟩
  change (project4 C' i).leader = true
  exact hi

theorem newFirePeaceful
    (hscan : PeacefulScanLocalityProp) :
    PPL.NewFirePeacefulProp := by
  intro n psi kappa hn3 hpsi ring C e i
  dsimp only
  intro hpost hold hnotmove
  let C' : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring C e
  have hshape :
      FourFieldStepCase ring
        (project4 C)
        (project4 C')
        e := by
    simpa [C'] using
      step_fourField_cases hn3 hpsi ring C e
  have hq :=
    hscan hn3 ring
      (project4 C)
      (project4 C')
      e
      hshape
  rcases hq.2 with ⟨hnew, hkeep⟩
  have hpost4 :
      (project4 C' i).bullet = (2 : Fin 3) := by
    change (C' i).bullet = (2 : Fin 3)
    simpa [C'] using hpost
  have hold4 :
      (project4 C i).bullet ≠ (2 : Fin 3) := by
    change (C i).bullet ≠ (2 : Fin 3)
    exact hold
  have hnotmove4 :
      Or
        (i ≠ ring.rightNeighbor e)
        ((project4 C e).bullet ≠ (2 : Fin 3)) := by
    rcases hnotmove with hne | hleft
    · exact Or.inl hne
    · exact Or.inr hleft
  have hp :=
    hnew i hpost4 hold4 hnotmove4
  change Peaceful4 ring (project4 C') i
  exact hp

theorem peacefulKeepPhysical
    (hscan : PeacefulScanLocalityProp) :
    PPL.PeacefulKeepPhysicalProp := by
  intro n psi kappa hn3 hpsi ring C e i hlive hpeace
  dsimp only
  let C' : Config n psi kappa :=
    PopulationProtocol.step (PPL.protocol psi kappa) ring C e
  have hshape :
      FourFieldStepCase ring
        (project4 C)
        (project4 C')
        e := by
    simpa [C'] using
      step_fourField_cases hn3 hpsi ring C e
  have hq :=
    hscan hn3 ring
      (project4 C)
      (project4 C')
      e
      hshape
  rcases hq.2 with ⟨hnew, hkeep⟩
  have hlive4 :
      (project4 C i).bullet = (2 : Fin 3) := by
    change (C i).bullet = (2 : Fin 3)
    exact hlive
  have hpeace4 :
      Peaceful4 ring (project4 C) i := by
    change PPL.Peaceful ring C i
    exact hpeace
  have hk :=
    hkeep i hlive4 hpeace4
  constructor
  · intro hpost
    have hpost4 :
        (project4 C' i).bullet = (2 : Fin 3) := by
      change (C' i).bullet = (2 : Fin 3)
      simpa [C'] using hpost
    have hp := hk.1 hpost4
    change Peaceful4 ring (project4 C') i
    exact hp
  · intro hie hpost hold
    have hpost4 :
        (project4 C' (ring.rightNeighbor e)).bullet =
          (2 : Fin 3) := by
      change (C' (ring.rightNeighbor e)).bullet =
        (2 : Fin 3)
      simpa [C'] using hpost
    have hold4 :
        (project4 C (ring.rightNeighbor e)).bullet ≠
          (2 : Fin 3) := by
      change (C (ring.rightNeighbor e)).bullet ≠
        (2 : Fin 3)
      exact hold
    have hp :=
      hk.2 hie hpost4 hold4
    change
      Peaceful4 ring
        (project4 C')
        (ring.rightNeighbor e)
    exact hp

/--
Unconditional with respect to PeacefulKeep's three former hypotheses:
they are instantiated by the three theorems above.  In this bounded draft the
single four-field scan leaf PeacefulScanLocalityProp remains explicit.
-/
theorem cpb_step_closed_uncond
    (hscan : PeacefulScanLocalityProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : CPB ring C) :
    CPB ring
      (PopulationProtocol.step
        (PPL.protocol psi kappa) ring C e) := by
  exact
    PPL.cpb_step_closed
      (cpbLeaderSurvival hscan)
      (newFirePeaceful hscan)
      (peacefulKeepPhysical hscan)
      hn3 hpsi ring C e hC

end PPL.Safety.PeacefulProps

#print axioms PPL.Safety.PeacefulProps.step_fourField_cases
#print axioms PPL.Safety.PeacefulProps.cpbLeaderSurvival
#print axioms PPL.Safety.PeacefulProps.newFirePeaceful
#print axioms PPL.Safety.PeacefulProps.peacefulKeepPhysical
#print axioms PPL.Safety.PeacefulProps.cpb_step_closed_uncond
