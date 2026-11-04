import Leader.PPL.ReachCPB.MismatchHistFreshPrefix
import Leader.PPL.TokenCompletion.GhostStepMirror
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
# Truth audit of Lemma16PostEpochFreshBranchRow

The row is false as currently quantified.

The live invariant's negative-half latch is indexed from b:

  (Cepoch (shiftRight ring b q)).id =
    lemma16ExpectedAddOneBit ring Cepoch k q.

But Lemma16PostEpochFreshBranchRow receives no premise relating b to the
actual c = 1 comparison site.  At q = 0 the target-prefix premise is vacuous.
Hence a q = 0 fresh token can make a matching c = 1 comparison at its real
responder, create no leader, enter the negative half, and immediately be
required to satisfy the latch at an unrelated b.

The closed n=4, psi=2 witness below realizes exactly this case.  It is
nonterminal: moves advances only from 1 to 2, whereas
tokenTrajectoryMoves 2 = 5.  Therefore job-598 fresh-terminal provenance
cannot repair this row.

The minimal static repair is to thread

  b = shiftRight ring k psi

from the bad-border geometry into this row.  Together with
Lemma16FreshMacroStageAt, a c = 1 owner at macro-stage q is at
shiftRight k (q + psi - 1), so its responder is exactly shiftRight b q.
This is the site whose Detect comparison decides whether to birth a leader
or install the latch.
-/

theorem q19912Hpsi : 2 ≤ 2 := by
  omega

def q19912Ring : DirectedRing 4 :=
  ⟨by omega⟩

def q19912E0 : Fin 4 :=
  ⟨0, by omega⟩

def q19912E1 : Fin 4 :=
  ⟨1, by omega⟩

def q19912E2 : Fin 4 :=
  ⟨2, by omega⟩

def q19912E3 : Fin 4 :=
  ⟨3, by omega⟩

def q19912Value : TokenData 2 :=
  ((offsetOneCode 2 q19912Hpsi, (1 : Fin 2)),
    (0 : Fin 2))

def q19912PostValue : TokenData 2 :=
  ((offsetNegPsiPlusOneCode 2 q19912Hpsi, (1 : Fin 2)),
    (0 : Fin 2))

def q19912Z : GhostToken 4 2 where
  value := q19912Value
  lmeta :=
    { id := .born .black 0
      birthSite := q19912E0
      birthStep := 0
      moves := 1 }

def q19912ZPost : GhostToken 4 2 where
  value := q19912PostValue
  lmeta :=
    { id := .born .black 0
      birthSite := q19912E0
      birthStep := 0
      moves := 2 }

/--
Canonical Detect geometry except for the deliberately unrelated choice
b = q19912E3.

The actual q=0 c=1 comparison occurs on edge E1 -> E2.  Its token bit and
the responder id are both true, so Algorithm 3 takes the matching branch and
does not call leaderBirth.  The unrelated site E3 has id=false.
-/
def q19912State (i : Fin 4) : State 2 1 :=
  { leader := false
    id := if i = q19912E2 then true else false
    dist := i
    last := false
    tokenB :=
      if i = q19912E1 then
        some q19912Value
      else
        none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := (0 : Fin 2)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }

def q19912C : Config 4 2 1 :=
  q19912State

def q19912G : GhostConfig 4 2 1 :=
  { phys := q19912C
    black := fun i =>
      if i = q19912E1 then
        some q19912Z
      else
        none
    white := fun _ => none
    completed := [] }

theorem q19912ValueOffset :
    decodeOffset 2 (tokenCode q19912Value) = (1 : Int) := by
  change
    decodeOffset 2
        (offsetOneCode 2 q19912Hpsi) =
      (1 : Int)
  exact decodeOffset_one 2 q19912Hpsi

theorem q19912PostValueOffset :
    decodeOffset 2 (tokenCode q19912PostValue) = (-1 : Int) := by
  change
    decodeOffset 2
        (offsetNegPsiPlusOneCode 2 q19912Hpsi) =
      (-1 : Int)
  rw [decodeOffset_negPsiPlusOne]
  omega

theorem q19912OwnerShape
    (i : Fin 4)
    (z : GhostToken 4 2)
    (h :
      ghostTokenAt .black q19912G i = some z) :
    i = q19912E1 ∧ z = q19912Z := by
  by_cases hi : i = q19912E1
  · subst i
    have hz : q19912Z = z := by
      simpa [q19912G, ghostTokenAt] using h
    exact ⟨rfl, hz.symm⟩
  · have hf : False := by
      simpa [q19912G, ghostTokenAt, hi] using h
    exact False.elim hf

theorem q19912InitialMacro :
    Lemma16FreshMacroStageAt
      q19912Ring q19912E0 q19912E1 q19912Z 0 := by
  unfold Lemma16FreshMacroStageAt
  dsimp only
  refine ⟨1, ?_, ?_⟩
  · decide
  · have hoff :
        decodeOffset 2
            (tokenCode q19912Z.value) =
          (1 : Int) := by
      simpa [q19912Z] using q19912ValueOffset
    rw [hoff]
    left
    simp [q19912Z]

theorem q19912Payload :
    payloadCorrect
      q19912Ring q19912C q19912E0 0
      q19912Value := by
  decide

theorem q19912PrefixZero :
    Lemma16TargetPrefix
      q19912Ring q19912C q19912E3 q19912E0 0 := by
  unfold Lemma16TargetPrefix
  intro x hx
  omega

theorem q19912StateInvariant :
    Lemma16PostEpochFreshStateInvariant
      q19912Ring q19912C 0
      q19912E3 q19912E0 .black q19912G := by
  unfold Lemma16PostEpochFreshStateInvariant
  refine ⟨?_, ?_⟩
  · intro i
    rfl
  · unfold Lemma16PostEpochFreshLiveInvariant
    intro i z t howner hid _hsite _hepoch _hprior
    rcases q19912OwnerShape i z howner with ⟨rfl, rfl⟩
    have ht : t = 0 := by
      change
        LineageId.born .black 0 =
          LineageId.born .black t at hid
      cases hid
      rfl
    subst t
    refine
      ⟨0, by omega, q19912InitialMacro,
        q19912Payload, q19912PrefixZero, ?_⟩
    intro hneg
    have hoff :
        decodeOffset 2
            (tokenCode q19912Z.value) =
          (1 : Int) := by
      simpa [q19912Z] using q19912ValueOffset
    rw [hoff] at hneg
    omega

theorem q19912Ready :
    DetectReadyCapped q19912Ring q19912G.phys := by
  decide

theorem q19912PostOwner :
    ghostTokenAt .black
        (ghostStep q19912Hpsi q19912Ring 1
          q19912G q19912E1)
        q19912E2 =
      some q19912ZPost := by
  decide

theorem q19912PostCompleted :
    (ghostStep q19912Hpsi q19912Ring 1
      q19912G q19912E1).completed = [] := by
  decide

theorem q19912PostNotCPB :
    ¬ CPB q19912Ring
        (ghostStep q19912Hpsi q19912Ring 1
          q19912G q19912E1).phys := by
  decide

theorem q19912PostNoPrior :
    Lemma16NoPriorCompletionId
      (ghostStep q19912Hpsi q19912Ring 1
        q19912G q19912E1)
      q19912ZPost.lmeta.id := by
  unfold Lemma16NoPriorCompletionId
  intro m hm
  rw [q19912PostCompleted] at hm
  simp at hm

theorem q19912ExpectedBit :
    lemma16ExpectedAddOneBit
        q19912Ring q19912C q19912E0 0 =
      true := by
  decide

theorem q19912WrongLatchSite :
    (q19912C
        (shiftRight q19912Ring q19912E3 0)).id =
      false := by
  decide

/--
The literal residual is false.

The witness reaches the negative half without CPB.  Its metadata and signed
offset force macro-stage q=0.  The resulting latch is then required at E3,
where the frozen id is false, while the expected add-one bit is true.
-/
theorem lemma16PostEpochFreshBranchRow_false :
    ¬ Lemma16PostEpochFreshBranchRow := by
  intro hrow
  have hout :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      q19912Hpsi
      (by omega : 3 ≤ 4)
      q19912Ring
      q19912C
      0
      q19912E3
      q19912E0
      .black
      1
      q19912G
      q19912E1
      q19912Ready
      q19912StateInvariant
  dsimp only at hout
  rcases hout with hcpb | hkeep
  · exact q19912PostNotCPB hcpb
  · have hlive :=
      hkeep.1
        q19912E2 q19912ZPost 0
        q19912PostOwner
        rfl rfl
        (by omega)
        q19912PostNoPrior
    rcases hlive with
      ⟨q, _hq, hmacro, _hpay,
        _hprefix, hlatch⟩

    have hq0 : q = 0 := by
      unfold Lemma16FreshMacroStageAt at hmacro
      dsimp only at hmacro
      have hoff :
          decodeOffset 2
              (tokenCode q19912ZPost.value) =
            (-1 : Int) := by
        simpa [q19912ZPost] using
          q19912PostValueOffset
      rw [hoff] at hmacro
      rcases hmacro with
        ⟨x, _hsite, hpos | hneg⟩
      · omega
      · have hmoves :
            2 =
              q * (2 * 2 - 1) +
                (2 * 2 - 1 - 1) := by
          simpa [q19912ZPost] using hneg.2.2.2
        omega

    subst q

    have hneg :
        decodeOffset 2
            (tokenCode q19912ZPost.value) < 0 := by
      have hoff :
          decodeOffset 2
              (tokenCode q19912ZPost.value) =
            (-1 : Int) := by
        simpa [q19912ZPost] using
          q19912PostValueOffset
      rw [hoff]
      omega

    have hbad := hlatch hneg
    rw [q19912WrongLatchSite, q19912ExpectedBit] at hbad
    cases hbad

/-!
## Minimal correction

The counterexample is excluded by the static border geometry below.  This is
the weakest useful fact at the c=1 branch: for macro-stage q, the actual
responder must be target site b+q.

A convenient stronger, q-independent premise is

  b = shiftRight ring k psi.

It should be derived once from LastReadyCapped plus the frozen bad-border
witness, then threaded through the suffix induction.  It is static, so
it needs no one-step preservation proof.
-/

def Lemma16PostEpochFreshBorderGeometry
    {n : Nat}
    (ring : DirectedRing n)
    (b k : Fin n)
    (psi : Nat) : Prop :=
  b = shiftRight ring k psi

theorem q19912MissingGeometry :
    ¬ Lemma16PostEpochFreshBorderGeometry
        q19912Ring q19912E3 q19912E0 2 := by
  unfold Lemma16PostEpochFreshBorderGeometry
  decide

/--
The geometry premise supplies exactly the missing comparison-site equality
for every c=1 macro-stage point.
-/
theorem lemma16FreshMacroStage_c1_responder_of_borderGeometry
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (b k i : Fin n)
    (z : GhostToken n psi)
    (q : Nat)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi)
    (hstage :
      Lemma16FreshMacroStageAt
        ring k i z q)
    (hc :
      decodeOffset psi (tokenCode z.value) = 1) :
    ring.rightNeighbor i =
      shiftRight ring b q := by
  unfold Lemma16PostEpochFreshBorderGeometry at hgeom
  unfold Lemma16FreshMacroStageAt at hstage
  dsimp only at hstage
  rw [hc] at hstage
  rcases hstage with
    ⟨x, hsite, hpos | hneg⟩
  · have hx :
        x = q + (psi - 1) := by
      simpa using hpos.2.2.1
    rw [hsite, hx, hgeom]
    apply Fin.ext
    unfold DirectedRing.rightNeighbor shiftRight
    simp only
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  · omega

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshBranchRow_false
#print axioms PPL.Convergence.ReachCPB.lemma16FreshMacroStage_c1_responder_of_borderGeometry
